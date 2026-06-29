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
///
/// # Reset Behavior!!
///
/// This module must not be used if warm reset capabily is a requirement. The
/// only execption is if you consistently use a reset controller that sequences
/// the resets while gating both clock domains (be very careful if you follow
/// this strategy!). If you need warm reset/clear/flush capabilities, use (AND
/// CAREFULLY READ THE DESCRIPTION) the cc_cdc_fifo_gray_clearable module.
///
/// After this disclaimer, here is how you connect the src_rst_ni and the
/// dst_rst_ni of this module for power-on-reset (POR). The src_rst_ni and
/// dst_rst_ni signal must be asserted SIMULTANEOUSLY (i.e. asynchronous
/// assertion). Othwerwise, spurious transactions could occur in the domain
/// where the reset arrives later than the other. The de-assertion of both reset
/// must be synchronized to their respective clock domain (i.e. src_rst_ni must
/// be deasserted synchronously to the src_clk_i and dst_rst_ni must be
/// deasserted synchronously to dst_clk_i.) You can use the cc_rstgen cell in the
/// common_cells library to achieve this (synchronization of only the
/// de-assertion). However be carefull about reset domain crossings; If you
/// reset both domain asynchronously in their entirety (i.e. POR) you are fine.
/// However, if you use this strategy for warm resets (some parts of the circuit
/// are not reset) you might introduce metastability in this separate
/// reset-domain when you assert the reset (the deassertion synchronizer doen't
/// help here).
///
/// # Constraints
///
/// We need to make sure that the propagation delay of the
/// data, read and write pointer is bound to the minimum of
/// either the sending or receiving clock period to prevent
/// an inconsistent state to be latched (if for example the one
/// bit of the read/write pointer have an excessive delay).
/// Furthermore, we should deactivate setup and hold checks on
/// the asynchronous signals.
///
/// ```
/// set_ungroup [get_designs cc_cdc_fifo_gray*] false
/// set_boundary_optimization [get_designs cc_cdc_fifo_gray*] false
/// set_max_delay min(T_src, T_dst) \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// set_false_path -hold \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// ```

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray #(
  /// The width of the default logic type.
  parameter int unsigned Width = 1,
  /// The data type of the payload transported by the FIFO.
  parameter type data_t = logic [Width-1:0],
  /// The FIFO's depth given as 2**LogDepth.
  parameter int unsigned LogDepth = 3,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int unsigned SyncStages = 2
) (
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i
);

  data_t [2**LogDepth-1:0] async_data;
  logic [LogDepth:0]  async_wptr;
  logic [LogDepth:0]  async_rptr;

  cc_cdc_fifo_gray_src #(
    .data_t   ( data_t   ),
    .LogDepth ( LogDepth )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_data_i,
    .src_valid_i,
    .src_ready_o,

    (* async *) .async_data_o ( async_data ),
    (* async *) .async_wptr_o ( async_wptr ),
    (* async *) .async_rptr_i ( async_rptr )
  );

  cc_cdc_fifo_gray_dst #(
    .data_t   ( data_t   ),
    .LogDepth ( LogDepth )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,

    (* async *) .async_data_i ( async_data ),
    (* async *) .async_wptr_i ( async_wptr ),
    (* async *) .async_rptr_o ( async_rptr )
  );

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_gt_2, SyncStages >= 2)
  `endif

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_src #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic  src_rst_ni,
  input  logic  src_clk_i,
  input  data_t src_data_i,
  input  logic  src_valid_i,
  output logic  src_ready_o,

  output data_t [2**LogDepth-1:0] async_data_o,
  output logic  [LogDepth:0]      async_wptr_o,
  input  logic  [LogDepth:0]      async_rptr_i
);

  localparam int unsigned PtrWidth = LogDepth+1;
  localparam logic [PtrWidth-1:0] PtrFull = (1 << LogDepth);

  data_t [2**LogDepth-1:0] data_q, data_d;
  logic [PtrWidth-1:0] wptr_q, wptr_d, wptr_bin, wptr_next, rptr, rptr_bin;

  // Data FIFO.
  assign async_data_o = data_q;

  always_comb begin
    data_d                          = data_q;
    data_d[wptr_bin[LogDepth-1:0]] = src_data_i;
  end
  `FFL(data_q, data_d, src_valid_i & src_ready_o, '0, src_clk_i, src_rst_ni)

  // Read pointer.
  for (genvar i = 0; i < PtrWidth; i++) begin : gen_sync
    tc_sync #(.Stages(SyncStages)) i_sync (
      .clk_i    ( src_clk_i       ),
      .rst_ni   ( src_rst_ni      ),
      .serial_i ( async_rptr_i[i] ),
      .serial_o ( rptr[i]         )
    );
  end
  cc_gray_to_binary #(PtrWidth) i_rptr_g2b (.a_i(rptr), .z_o(rptr_bin));

  // Write pointer.
  assign wptr_next = wptr_bin+1;
  cc_gray_to_binary #(PtrWidth) i_wptr_g2b (.a_i(wptr_q), .z_o(wptr_bin));
  cc_binary_to_gray #(PtrWidth) i_wptr_b2g (.a_i(wptr_next), .z_o(wptr_d));
  `FFL(wptr_q, wptr_d, src_valid_i & src_ready_o, '0, src_clk_i, src_rst_ni)
  assign async_wptr_o = wptr_q;

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((wptr_bin ^ rptr_bin) != PtrFull);

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cc_cdc_fifo_gray_dst #(
  parameter type data_t = logic,
  parameter int unsigned LogDepth = 3,
  parameter int unsigned SyncStages = 2
)(
  input  logic  dst_rst_ni,
  input  logic  dst_clk_i,
  output data_t dst_data_o,
  output logic  dst_valid_o,
  input  logic  dst_ready_i,

  input  data_t [2**LogDepth-1:0] async_data_i,
  input  logic  [LogDepth:0]      async_wptr_i,
  output logic  [LogDepth:0]      async_rptr_o
);

  localparam int unsigned PtrWidth = LogDepth+1;
  localparam logic [PtrWidth-1:0] PtrEmpty = '0;

  data_t dst_data;
  logic [PtrWidth-1:0] rptr_q, rptr_d, rptr_bin, rptr_bin_d, rptr_next, wptr, wptr_bin;
  logic dst_valid, dst_ready;
  // Data selector and register.
  assign dst_data = async_data_i[rptr_bin[LogDepth-1:0]];

  // Read pointer.
  assign rptr_next = rptr_bin+1;
  cc_gray_to_binary #(PtrWidth) i_rptr_g2b (.a_i(rptr_q), .z_o(rptr_bin));
  cc_binary_to_gray #(PtrWidth) i_rptr_b2g (.a_i(rptr_next), .z_o(rptr_d));
  `FFL(rptr_q, rptr_d, dst_valid & dst_ready, '0, dst_clk_i, dst_rst_ni)
  assign async_rptr_o = rptr_q;

  // Write pointer.
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
  assign dst_valid = ((wptr_bin ^ rptr_bin) != PtrEmpty);

  // Cut the combinatorial path with a spill register.
  cc_spill_register #(
    .data_t  ( data_t )
  ) i_spill_register (
    .clk_i   ( dst_clk_i   ),
    .rst_ni  ( dst_rst_ni  ),
    .clr_i   ( '0          ),
    .valid_i ( dst_valid   ),
    .ready_o ( dst_ready   ),
    .data_i  ( dst_data    ),
    .valid_o ( dst_valid_o ),
    .ready_i ( dst_ready_i ),
    .data_o  ( dst_data_o  )
  );

endmodule
