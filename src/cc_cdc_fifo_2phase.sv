// Copyright 2018 ETH Zurich and University of Bologna.
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

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

/// A clock domain crossing FIFO, using 2-phase hand shakes.
///
/// This FIFO has its push and pop ports in two separate clock domains. Its size
/// can only be powers of two, which is why its depth is given as 2**LogDepth.
/// LogDepth must be at least 1.
///
/// # Reset Behavior!!
///
/// This module must not be used if warm reset capabily is a requirement. The
/// only execption is if you consistently use a reset controller that sequences
/// the resets while gating both clock domains (be very careful if you follow
/// this strategy!).
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
/// de-assertion). However, be careful about reset domain crossings; If you
/// reset both domain asynchronously in their entirety (i.e. POR) you are fine.
/// However, if you use this strategy for warm resets (some parts of the circuit
/// are not reset) you might introduce metastability in this separate
/// reset-domain when you assert the reset (the deassertion synchronizer doen't
/// help here).
///
/// CONSTRAINT: Requires max_delay of min_period(src_clk_i, dst_clk_i) through
/// async_wptr_req, async_wptr_ack, async_wptr_data, async_rptr_req,
/// async_rptr_ack, async_rptr_data, and async_data. The async_wptr_* and
/// async_rptr_* signals are the actual pointer handshakes, while async_data is
/// the FIFO storage exposed from the source domain to the destination domain.
module cc_cdc_fifo_2phase #(
  /// The data type of the payload transported by the FIFO.
  parameter type data_t = logic,
  /// The FIFO's depth given as 2**LogDepth.
  parameter int unsigned LogDepth = 3,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int unsigned SyncStages = 2
)(
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

  localparam int unsigned PtrWidth = LogDepth+1;
  typedef logic [PtrWidth-1:0] pointer_t;

  data_t [2**LogDepth-1:0] async_data;
  logic async_wptr_req;
  logic async_wptr_ack;
  pointer_t async_wptr_data;
  logic async_rptr_req;
  logic async_rptr_ack;
  pointer_t async_rptr_data;

  cc_cdc_fifo_2phase_src #(
    .data_t     ( data_t     ),
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_src (
    .src_rst_ni   ( src_rst_ni  ),
    .src_clk_i    ( src_clk_i   ),
    .src_data_i   ( src_data_i  ),
    .src_valid_i  ( src_valid_i ),
    .src_ready_o  ( src_ready_o ),

    (* async *) .async_data_o      ( async_data       ),
    (* async *) .async_wptr_req_o  ( async_wptr_req   ),
    (* async *) .async_wptr_ack_i  ( async_wptr_ack   ),
    (* async *) .async_wptr_data_o ( async_wptr_data  ),
    (* async *) .async_rptr_req_i  ( async_rptr_req   ),
    (* async *) .async_rptr_ack_o  ( async_rptr_ack   ),
    (* async *) .async_rptr_data_i ( async_rptr_data  )
  );

  cc_cdc_fifo_2phase_dst #(
    .data_t     ( data_t     ),
    .LogDepth   ( LogDepth   ),
    .SyncStages ( SyncStages )
  ) i_dst (
    .dst_rst_ni   ( dst_rst_ni  ),
    .dst_clk_i    ( dst_clk_i   ),
    .dst_data_o   ( dst_data_o  ),
    .dst_valid_o  ( dst_valid_o ),
    .dst_ready_i  ( dst_ready_i ),

    (* async *) .async_data_i      ( async_data       ),
    (* async *) .async_wptr_req_i  ( async_wptr_req   ),
    (* async *) .async_wptr_ack_o  ( async_wptr_ack   ),
    (* async *) .async_wptr_data_i ( async_wptr_data  ),
    (* async *) .async_rptr_req_o  ( async_rptr_req   ),
    (* async *) .async_rptr_ack_i  ( async_rptr_ack   ),
    (* async *) .async_rptr_data_o ( async_rptr_data  )
  );

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_gt_2, SyncStages >= 2)
  `endif

endmodule


/// Source side for the 2-phase CDC FIFO.
module cc_cdc_fifo_2phase_src #(
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
  output logic                    async_wptr_req_o,
  input  logic                    async_wptr_ack_i,
  output logic [LogDepth:0]       async_wptr_data_o,
  input  logic                    async_rptr_req_i,
  output logic                    async_rptr_ack_o,
  input  logic [LogDepth:0]       async_rptr_data_i
);

  localparam int unsigned PtrWidth = LogDepth+1;
  typedef logic [PtrWidth-1:0] pointer_t;
  typedef logic [LogDepth-1:0] index_t;

  localparam pointer_t PtrFull = (1 << LogDepth);

  index_t fifo_widx;
  logic fifo_write;
  data_t [2**LogDepth-1:0] fifo_data_q;

  pointer_t src_wptr_q;
  pointer_t src_rptr;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  assign fifo_widx = src_wptr_q[LogDepth-1:0];
  assign fifo_write = src_valid_i && src_ready_o;
  assign async_data_o = fifo_data_q;

  for (genvar i = 0; i < 2**LogDepth; i++) begin : gen_word
    always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
      if (!src_rst_ni) begin
        fifo_data_q[i] <= data_t'('0);
      end else if (fifo_write && (fifo_widx == i)) begin
        fifo_data_q[i] <= src_data_i;
      end
    end
  end

  `FFL(src_wptr_q, src_wptr_q + 1, fifo_write, '0, src_clk_i, src_rst_ni)

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((src_wptr_q ^ src_rptr) != PtrFull);

  cc_cdc_2phase_src #(
    .data_t     ( pointer_t  ),
    .SyncStages ( SyncStages )
  ) i_cdc_wptr_src (
    .rst_ni       ( src_rst_ni        ),
    .clk_i        ( src_clk_i         ),
    .data_i       ( src_wptr_q        ),
    .valid_i      ( 1'b1              ),
    .ready_o      (                   ),
    .async_req_o  ( async_wptr_req_o  ),
    .async_ack_i  ( async_wptr_ack_i  ),
    .async_data_o ( async_wptr_data_o )
  );

  cc_cdc_2phase_dst #(
    .data_t     ( pointer_t  ),
    .SyncStages ( SyncStages )
  ) i_cdc_rptr_dst (
    .rst_ni       ( src_rst_ni        ),
    .clk_i        ( src_clk_i         ),
    .data_o       ( src_rptr          ),
    .valid_o      (                   ),
    .ready_i      ( 1'b1              ),
    .async_req_i  ( async_rptr_req_i  ),
    .async_ack_o  ( async_rptr_ack_o  ),
    .async_data_i ( async_rptr_data_i )
  );

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_gt_2, SyncStages >= 2)
  `endif

endmodule


/// Destination side for the 2-phase CDC FIFO.
module cc_cdc_fifo_2phase_dst #(
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
  input  logic                    async_wptr_req_i,
  output logic                    async_wptr_ack_o,
  input  logic [LogDepth:0]       async_wptr_data_i,
  output logic                    async_rptr_req_o,
  input  logic                    async_rptr_ack_i,
  output logic [LogDepth:0]       async_rptr_data_o
);

  localparam int unsigned PtrWidth = LogDepth+1;
  typedef logic [PtrWidth-1:0] pointer_t;
  typedef logic [LogDepth-1:0] index_t;

  localparam pointer_t PtrEmpty = '0;

  index_t fifo_ridx;
  data_t fifo_rdata;

  pointer_t dst_wptr;
  pointer_t dst_rptr_q;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  assign fifo_ridx = dst_rptr_q[LogDepth-1:0];
  assign fifo_rdata = async_data_i[fifo_ridx];
  assign dst_data_o = fifo_rdata;

  `FFL(dst_rptr_q, dst_rptr_q + 1, dst_valid_o && dst_ready_i, '0, dst_clk_i, dst_rst_ni)

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign dst_valid_o = ((dst_rptr_q ^ dst_wptr) != PtrEmpty);

  cc_cdc_2phase_dst #(
    .data_t     ( pointer_t  ),
    .SyncStages ( SyncStages )
  ) i_cdc_wptr_dst (
    .rst_ni       ( dst_rst_ni        ),
    .clk_i        ( dst_clk_i         ),
    .data_o       ( dst_wptr          ),
    .valid_o      (                   ),
    .ready_i      ( 1'b1              ),
    .async_req_i  ( async_wptr_req_i  ),
    .async_ack_o  ( async_wptr_ack_o  ),
    .async_data_i ( async_wptr_data_i )
  );

  cc_cdc_2phase_src #(
    .data_t     ( pointer_t  ),
    .SyncStages ( SyncStages )
  ) i_cdc_rptr_src (
    .rst_ni       ( dst_rst_ni        ),
    .clk_i        ( dst_clk_i         ),
    .data_i       ( dst_rptr_q        ),
    .valid_i      ( 1'b1              ),
    .ready_o      (                   ),
    .async_req_o  ( async_rptr_req_o  ),
    .async_ack_i  ( async_rptr_ack_i  ),
    .async_data_o ( async_rptr_data_o )
  );

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LogDepth > 0)
  `ASSERT_INIT(sync_stages_gt_2, SyncStages >= 2)
  `endif

endmodule
