// Copyright 2018-2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Manuel Eggimann <meggimann@iis.ee.ethz.ch> (clearability feature)
// Philippe Sauter <phsauter@iis.ee.ethz.ch> (source/destination split)

/// A clock domain crossing FIFO, using gray counters.
///
/// # Architecture
///
/// The design is split into two parts, each one being clocked and reset
/// separately.
/// 1. The data to be transferred  over the clock domain boundary is
///    is stored in a FIFO. The corresponding write pointer is managed
///    (incremented) in the source clock domain.
/// 2. The entire FIFO content is exposed over the `async_data` port.
///    The destination clock domain increments its read pointer
///    in its destination clock domain.
///
/// Read and write pointers are then gray coded, communicated
/// and synchronized using a classic multi-stage FF synchronizer
/// in the other clock domain. The gray coding ensures that only
/// one bit changes at each pointer increment, preventing the
/// synchronizer to accidentally latch an inconsistent state
/// on a multi-bit bus.
///
/// The not full signal e.g. `src_ready_o` (on the sending side)
/// is generated using the local write pointer and the pessimistic
/// read pointer from the destination clock domain (pessimistic
/// because it is delayed at least two cycles because of the synchronizer
/// stages). This prevents the FIFO from overflowing.
///
/// The not empty signal e.g. `dst_valid_o` is generated using
/// the pessimistic write pointer and the local read pointer in
/// the destination clock domain. This means the FIFO content
/// does not need to be synchronized as we are sure we are reading
/// data which has been written at least two cycles earlier.
/// Furthermore, the read select logic into the FIFO is completely
/// clocked by the destination clock domain which avoids
/// inefficient data synchronization.
///
/// The FIFO size must be powers of two, which is why its depth is
/// given as 2**LogDepth. LogDepth must be at least 1.

/// Reset Behavior:
///
/// In contrast to the cc_cdc_fifo_gray version without clear signal, this module
/// supports one-sided warm resets (asynchronously and synchronously). The way
/// this is implemented is described in more detail in the cc_cdc_reset_ctrlr
/// module. To summarize a synchronous clear request i.e. src/dst_clear_i will
/// cause the respective other clock domain to reset as well without introducing
/// any spurious transactions. This is acomplished by an internal module
/// (cc_cdc_reset_ctrlr) the starts a reset sequence on both sides of the CDC in
/// lock-step that first isolates the CDC from the outside world and then resets
/// it. The reset sequencer provides the following behavior:
/// 1. There are no spurious invalid or duplicated transactions regardless how
///    the individual sides are reset (can also happen roughly simultaneosly)
/// 2. The FIFO becomes unready at the src side in the next cycle after
///    synchronous reset request until the reset sequence is completed. Some of
///    the pending transactions might still complete (if the dst accepts at the
///    exact time the reset is request on the src die), some of them will be
///    dropped (of course still guaranteeing FIFO order).
/// 3. During the reset sequence the dst might withdraw the valid signal. This
///    might violate higher level protocols. If you need this feature you would
///    have to path the existing implementation to wait with the isolate_ack
///    assertion until all open handshakes were acknowledged.
/// 4. If the parameter ClearOnAsyncReset is enabled, the same behavior as
///    above is also valid for asynchronous resets on either side. However, this
///    increases the minimum number of synchronization stages (SyncStages
///    parameter) from 2 to 3 (read the cc_cdc_reset_ctrlr header to figure out
///    why).
///
///
/// # Constraints
///
/// We need to make sure that the propagation delay of the data, read and write
/// pointer is bound to the minimum of either the sending or receiving clock
/// period to prevent an inconsistent state to be latched (if for example the
/// one bit of the read/write pointer have an excessive delay). Furthermore, we
/// should deactivate setup and hold checks on the asynchronous signals.
///
/// async_data, async_wptr, and async_rptr are the FIFO storage and pointer CDCs
/// for the actual data path. async_reset_src2dst_req,
/// async_reset_dst2src_ack, async_reset_src2dst_next_phase,
/// async_reset_dst2src_req, async_reset_src2dst_ack, and
/// async_reset_dst2src_next_phase are the CDCs for the clearing state machines.
///
/// ``` set_ungroup [get_designs cc_cdc_fifo_gray*] false set_boundary_optimization
/// [get_designs cc_cdc_fifo_gray*] false set_max_delay min(T_src, T_dst) \
/// -through [get_pins -hierarchical -filter async] \ -through [get_pins
/// -hierarchical -filter async] set_false_path -hold \ -through [get_pins
/// -hierarchical -filter async] \ -through [get_pins -hierarchical -filter
/// async] ```

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_clearable #(
  /// The width of the default logic type.
  parameter int unsigned Width = 1,
  /// The data type of the payload transported by the FIFO.
  parameter type data_t = logic [Width-1:0],
  /// The FIFO's depth given as 2**LogDepth.
  parameter int unsigned LogDepth = 3,
  /// The number of synchronization registers to insert on the async pointers
  /// between the FIFOs. If ClearOnAsyncReset is enabled, we need at least 3
  /// synchronizer stages to provide the clear synchronizer lower latency than
  /// the async reset. I.e. if ClearOnAsyncReset==1 -> SyncStages >= 3 else
  /// SyncStages >= 2.
  parameter int unsigned SyncStages = 3,
  parameter bit ClearOnAsyncReset = 1
) (
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  logic  src_clear_i,
  output logic  src_clear_pending_o,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  input  logic  dst_clear_i,
  output logic  dst_clear_pending_o,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i
);

  data_t [2**LogDepth-1:0] async_data;
  logic [LogDepth:0]  async_wptr;
  logic [LogDepth:0]  async_rptr;
  cc_pkg::cdc_clear_seq_phase_e async_reset_src2dst_next_phase;
  logic async_reset_src2dst_req;
  logic async_reset_dst2src_ack;
  cc_pkg::cdc_clear_seq_phase_e async_reset_dst2src_next_phase;
  logic async_reset_dst2src_req;
  logic async_reset_src2dst_ack;

  if (ClearOnAsyncReset) begin : gen_elaboration_assertion
    if (SyncStages < 3)
      $error("The clearable CDC FIFO with async reset synchronization requires at least",
             "3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_elaboration_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  if (2*SyncStages > 2**LogDepth) begin : gen_elaboration_assertion2
    $warning("The FIFOs depth of %0d is insufficient to completely hide the latency of",
             " %0d SyncStages. The FIFO will stall in the case where f_src ~= f_dst. ",
             "It is reccomended to increase the FIFO's log depth to at least %0d.",
             2**LogDepth, SyncStages, $clog2(2*SyncStages));
  end



  cc_cdc_fifo_gray_clearable_src #(
    .data_t            ( data_t            ),
    .LogDepth          ( LogDepth          ),
    .SyncStages        ( SyncStages        ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_clear_i,
    .src_clear_pending_o,
    .src_data_i,
    .src_valid_i,
    .src_ready_o,

    (* async *) .async_data_o              ( async_data                   ),
    (* async *) .async_wptr_o              ( async_wptr                   ),
    (* async *) .async_rptr_i              ( async_rptr                   ),
    (* async *) .async_reset_next_phase_o  ( async_reset_src2dst_next_phase ),
    (* async *) .async_reset_req_o         ( async_reset_src2dst_req        ),
    (* async *) .async_reset_ack_i         ( async_reset_dst2src_ack        ),
    (* async *) .async_reset_next_phase_i  ( async_reset_dst2src_next_phase ),
    (* async *) .async_reset_req_i         ( async_reset_dst2src_req        ),
    (* async *) .async_reset_ack_o         ( async_reset_src2dst_ack        )
  );

  cc_cdc_fifo_gray_clearable_dst #(
    .data_t            ( data_t            ),
    .LogDepth          ( LogDepth          ),
    .SyncStages        ( SyncStages        ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i,
    .dst_clear_pending_o,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,

    (* async *) .async_data_i              ( async_data                   ),
    (* async *) .async_wptr_i              ( async_wptr                   ),
    (* async *) .async_rptr_o              ( async_rptr                   ),
    (* async *) .async_reset_next_phase_o  ( async_reset_dst2src_next_phase ),
    (* async *) .async_reset_req_o         ( async_reset_dst2src_req        ),
    (* async *) .async_reset_ack_i         ( async_reset_src2dst_ack        ),
    (* async *) .async_reset_next_phase_i  ( async_reset_src2dst_next_phase ),
    (* async *) .async_reset_req_i         ( async_reset_src2dst_req        ),
    (* async *) .async_reset_ack_o         ( async_reset_dst2src_ack        )
  );

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_lt_2, SyncStages >= 2)
  `endif

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_clearable_src #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2,
  parameter bit ClearOnAsyncReset = 1
)(
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  logic  src_clear_i,
  output logic  src_clear_pending_o,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  output data_t [2**LogDepth-1:0] async_data_o,
  output logic  [LogDepth:0]      async_wptr_o,
  input  logic  [LogDepth:0]      async_rptr_i,
  output cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_o,
  output logic async_reset_req_o,
  input  logic async_reset_ack_i,
  input  cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_i,
  input  logic async_reset_req_i,
  output logic async_reset_ack_o
);

  logic src_clear_req;
  logic src_clear_ack_q;
  logic src_ready;
  logic src_isolate_req;
  logic src_isolate_ack_q;

  if (ClearOnAsyncReset) begin : gen_elaboration_assertion
    if (SyncStages < 3)
      $error("The clearable CDC FIFO with async reset synchronization requires at least",
             "3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_sync_stage_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  localparam int unsigned ResetSyncStages = (SyncStages > 2) ? SyncStages - 1 : 2;

  cc_cdc_reset_ctrlr_half #(
    .SyncStages        ( ResetSyncStages    ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_cdc_reset_ctrlr_half (
    .clk_i              ( src_clk_i                  ),
    .rst_ni             ( src_rst_ni                 ),
    .clear_i            ( src_clear_i                ),
    .clear_o            ( src_clear_req              ),
    .clear_ack_i        ( src_clear_ack_q            ),
    .isolate_o          ( src_isolate_req            ),
    .isolate_ack_i      ( src_isolate_ack_q          ),
    (* async *) .async_next_phase_o ( async_reset_next_phase_o ),
    (* async *) .async_req_o        ( async_reset_req_o        ),
    (* async *) .async_ack_i        ( async_reset_ack_i        ),
    (* async *) .async_next_phase_i ( async_reset_next_phase_i ),
    (* async *) .async_req_i        ( async_reset_req_i        ),
    (* async *) .async_ack_o        ( async_reset_ack_o        )
  );

  cc_cdc_fifo_gray_src_clearable #(
    .data_t     ( data_t     ),
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_clear_i ( src_clear_req                  ),
    .src_data_i,
    .src_valid_i ( src_valid_i & !src_isolate_req ),
    .src_ready_o ( src_ready                      ),

    (* async *) .async_data_o ( async_data_o ),
    (* async *) .async_wptr_o ( async_wptr_o ),
    (* async *) .async_rptr_i ( async_rptr_i )
  );

  assign src_ready_o = src_ready & !src_isolate_req;

  // Isolation and clear are acknowledged one cycle after the local request.
  `FF(src_isolate_ack_q, src_isolate_req, 1'b0, src_clk_i, src_rst_ni)
  `FF(src_clear_ack_q,   src_clear_req,   1'b0, src_clk_i, src_rst_ni)

  assign src_clear_pending_o = src_isolate_req;

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_clearable_dst #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2,
  parameter bit ClearOnAsyncReset = 1
)(
  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  input  logic  dst_clear_i,
  output logic  dst_clear_pending_o,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i,

  input  data_t [2**LogDepth-1:0] async_data_i,
  input  logic  [LogDepth:0]      async_wptr_i,
  output logic  [LogDepth:0]      async_rptr_o,
  output cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_o,
  output logic async_reset_req_o,
  input  logic async_reset_ack_i,
  input  cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_i,
  input  logic async_reset_req_i,
  output logic async_reset_ack_o
);

  logic dst_clear_req;
  logic dst_clear_ack_q;
  logic dst_valid;
  logic dst_isolate_req;
  logic dst_isolate_ack_q;

  if (ClearOnAsyncReset) begin : gen_elaboration_assertion
    if (SyncStages < 3)
      $error("The clearable CDC FIFO with async reset synchronization requires at least",
             "3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_sync_stage_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  localparam int unsigned ResetSyncStages = (SyncStages > 2) ? SyncStages - 1 : 2;

  cc_cdc_reset_ctrlr_half #(
    .SyncStages        ( ResetSyncStages    ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_cdc_reset_ctrlr_half (
    .clk_i              ( dst_clk_i                  ),
    .rst_ni             ( dst_rst_ni                 ),
    .clear_i            ( dst_clear_i                ),
    .clear_o            ( dst_clear_req              ),
    .clear_ack_i        ( dst_clear_ack_q            ),
    .isolate_o          ( dst_isolate_req            ),
    .isolate_ack_i      ( dst_isolate_ack_q          ),
    (* async *) .async_next_phase_o ( async_reset_next_phase_o ),
    (* async *) .async_req_o        ( async_reset_req_o        ),
    (* async *) .async_ack_i        ( async_reset_ack_i        ),
    (* async *) .async_next_phase_i ( async_reset_next_phase_i ),
    (* async *) .async_req_i        ( async_reset_req_i        ),
    (* async *) .async_ack_o        ( async_reset_ack_o        )
  );

  cc_cdc_fifo_gray_dst_clearable #(
    .data_t     ( data_t     ),
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i ( dst_clear_req                  ),
    .dst_data_o,
    .dst_valid_o ( dst_valid                      ),
    .dst_ready_i ( dst_ready_i & !dst_isolate_req ),

    (* async *) .async_data_i ( async_data_i ),
    (* async *) .async_wptr_i ( async_wptr_i ),
    (* async *) .async_rptr_o ( async_rptr_o )
  );

  assign dst_valid_o = dst_valid & !dst_isolate_req;

  // Isolation and clear are acknowledged one cycle after the local request.
  `FF(dst_isolate_ack_q, dst_isolate_req, 1'b0, dst_clk_i, dst_rst_ni)
  `FF(dst_clear_ack_q,   dst_clear_req,   1'b0, dst_clk_i, dst_rst_ni)

  assign dst_clear_pending_o = dst_isolate_req;

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_src_clearable #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  logic  src_clear_i,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  output data_t [2**LogDepth-1:0] async_data_o,
  output logic  [LogDepth:0]      async_wptr_o,
  input  logic  [LogDepth:0]      async_rptr_i
);

  logic [LogDepth-1:0] src_widx;
  logic src_write;

  assign src_write = src_valid_i & src_ready_o;

  cc_cdc_fifo_gray_src_data_clearable #(
    .data_t   ( data_t   ),
    .LogDepth ( LogDepth )
  ) i_src_data (
    .src_rst_ni,
    .src_clk_i,
    .src_data_i,
    .src_widx_i  ( src_widx     ),
    .src_write_i ( src_write    ),
    .async_data_o
  );

  cc_cdc_fifo_gray_src_ptr_clearable #(
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_src_ptr (
    .src_rst_ni,
    .src_clk_i,
    .src_clear_i,
    .src_valid_i,
    .src_ready_o,
    .src_widx_o  ( src_widx     ),
    .async_wptr_o,
    .async_rptr_i
  );

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_dst_clearable #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  input  logic  dst_clear_i,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i,

  input  data_t [2**LogDepth-1:0] async_data_i,
  input  logic  [LogDepth:0]      async_wptr_i,
  output logic  [LogDepth:0]      async_rptr_o
);

  logic dst_valid, dst_ready;
  logic [LogDepth-1:0] dst_ridx;

  cc_cdc_fifo_gray_dst_ptr_clearable #(
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_dst_ptr (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i,
    .dst_ready_i ( dst_ready    ),
    .dst_valid_o ( dst_valid    ),
    .dst_ridx_o  ( dst_ridx     ),
    .async_wptr_i,
    .async_rptr_o
  );

  cc_cdc_fifo_gray_dst_data_clearable #(
    .data_t   ( data_t   ),
    .LogDepth ( LogDepth )
  ) i_dst_data (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,
    .dst_valid_i ( dst_valid    ),
    .dst_ready_o ( dst_ready    ),
    .dst_ridx_i  ( dst_ridx     ),
    .async_data_i
  );

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_src_data_clearable #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3
)(
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  data_t src_data_i,
  input  logic [LogDepth-1:0] src_widx_i,
  input  logic  src_write_i,
  output data_t [2**LogDepth-1:0] async_data_o
);

  data_t [2**LogDepth-1:0] data_d, data_q;

  always_comb begin
    data_d = data_q;
    data_d[src_widx_i] = src_data_i;
  end

  `FFL(data_q, data_d, src_write_i, '0, src_clk_i, src_rst_ni)

  assign async_data_o = data_q;

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_src_ptr_clearable #(
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  output logic [LogDepth-1:0] src_widx_o,
  output logic [LogDepth:0]   async_wptr_o,
  input  logic [LogDepth:0]   async_rptr_i
);

  localparam int unsigned PtrWidth = LogDepth+1;
  localparam logic [PtrWidth-1:0] PtrFull = (1 << LogDepth);

  logic [PtrWidth-1:0] wptr_q, wptr_d, wptr_bin, wptr_next, rptr, rptr_bin;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  // Read pointer from the destination domain, synchronized into the source
  // domain for the full check.
  for (genvar i = 0; i < PtrWidth; i++) begin : gen_sync
    tc_sync #(.Stages(SyncStages)) i_sync (
      .clk_i    ( src_clk_i       ),
      .rst_ni   ( src_rst_ni      ),
      .serial_i ( async_rptr_i[i] ),
      .serial_o ( rptr[i]         )
    );
  end
  cc_gray_to_binary #(PtrWidth) i_rptr_g2b (.a_i(rptr), .z_o(rptr_bin));

  // Local write pointer.
  assign wptr_next = wptr_bin+1;
  cc_gray_to_binary #(PtrWidth) i_wptr_g2b (.a_i(wptr_q), .z_o(wptr_bin));
  cc_binary_to_gray #(PtrWidth) i_wptr_b2g (.a_i(wptr_next), .z_o(wptr_d));
  `FFLARNC(wptr_q, wptr_d, src_valid_i & src_ready_o, src_clear_i, '0, src_clk_i, src_rst_ni)

  assign src_widx_o   = wptr_bin[LogDepth-1:0];
  assign async_wptr_o = wptr_q;

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((wptr_bin ^ rptr_bin) != PtrFull);

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_dst_ptr_clearable #(
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  input  logic dst_ready_i,
  output logic dst_valid_o,
  output logic [LogDepth-1:0] dst_ridx_o,
  input  logic [LogDepth:0]   async_wptr_i,
  output logic [LogDepth:0]   async_rptr_o
);

  localparam int unsigned PtrWidth = LogDepth+1;
  localparam logic [PtrWidth-1:0] PtrEmpty = '0;

  logic [PtrWidth-1:0] rptr_q, rptr_d, rptr_bin, rptr_next, wptr, wptr_bin;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  // Local read pointer.
  assign rptr_next = rptr_bin+1;
  cc_gray_to_binary #(PtrWidth) i_rptr_g2b (.a_i(rptr_q), .z_o(rptr_bin));
  cc_binary_to_gray #(PtrWidth) i_rptr_b2g (.a_i(rptr_next), .z_o(rptr_d));
  `FFLARNC(rptr_q, rptr_d, dst_valid_o & dst_ready_i, dst_clear_i, '0, dst_clk_i, dst_rst_ni)

  assign dst_ridx_o   = rptr_bin[LogDepth-1:0];
  assign async_rptr_o = rptr_q;

  // Write pointer from the source domain, synchronized into the destination
  // domain for the empty check.
  for (genvar i = 0; i < PtrWidth; i++) begin : gen_sync
    tc_sync #(.Stages(SyncStages)) i_sync (
      .clk_i    ( dst_clk_i       ),
      .rst_ni   ( dst_rst_ni      ),
      .serial_i ( async_wptr_i[i] ),
      .serial_o ( wptr[i]         )
    );
  end
  cc_gray_to_binary #(PtrWidth) i_wptr_g2b (.a_i(wptr), .z_o(wptr_bin));

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign dst_valid_o = ((wptr_bin ^ rptr_bin) != PtrEmpty);

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_dst_data_clearable #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3
)(
  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  input  logic  dst_clear_i,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i,
  input  logic  dst_valid_i,
  output logic  dst_ready_o,
  input  logic [LogDepth-1:0] dst_ridx_i,
  input  data_t [2**LogDepth-1:0] async_data_i
);

  data_t dst_data;

  assign dst_data = async_data_i[dst_ridx_i];

  // Cut the combinatorial path with a spill register.
  cc_spill_register_flushable #(
    .data_t  ( data_t )
  ) i_spill_register (
    .clk_i   ( dst_clk_i                ),
    .rst_ni  ( dst_rst_ni               ),
    .clr_i   ( '0                       ),
    .flush_i ( dst_clear_i              ),
    .valid_i ( dst_valid_i & !dst_clear_i ),
    .ready_o ( dst_ready_o              ),
    .data_i  ( dst_data                 ),
    .valid_o ( dst_valid_o              ),
    .ready_i ( dst_ready_i              ),
    .data_o  ( dst_data_o               )
  );

endmodule
