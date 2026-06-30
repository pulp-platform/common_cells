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
// Authors:
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch> (original CDC)
// - Manuel Eggimann <meggimann@iis.ee.ethz.ch> (clearability feature)
// - Philippe Sauter <phsauter@iis.ee.ethz.ch> (source/destination split)
//
// Description: Clearable Two-Phase CDC
// Transfer payloads with a two-phase handshake while coordinating synchronous
// and optional asynchronous one-sided clears across source and destination.

/// A two-phase clock domain crossing.
///
/// CONSTRAINT: Requires max_delay of min_period(src_clk_i, dst_clk_i) through
/// all asynchronous paths between the domains. The payload CDC uses
/// async_payload_req, async_payload_ack, and async_payload_data for the actual
/// data handshake. The clear sequencer CDCs use async_reset_src2dst_req,
/// async_reset_dst2src_ack, async_reset_src2dst_next_phase,
/// async_reset_dst2src_req, async_reset_src2dst_ack, and
/// async_reset_dst2src_next_phase to handshake the clearing state machines.
///
///
/// Reset Behavior:
///
/// In contrast to the cc_cdc_2phase version without clear signal, this module
/// supports one-sided warm resets (asynchronously and synchronously). The way
/// this is implemented is described in more detail in the cc_cdc_reset_ctrlr
/// module. To summarize a synchronous clear request i.e. src/dst_clear_i will
/// cause the respective other clock domain to reset as well without introducing
/// any spurious transactions. This is acomplished by an internal module
/// (cc_cdc_reset_ctrlr) that starts a reset sequence on both sides of the CDC in
/// lock-step that first isolates the CDC from the outside world and then resets
/// it. The reset sequencer provides the following behavior:
/// 1. There are no spurious invalid or duplicated transactions regardless how
///    the individual sides are reset (can also happen roughly simultaneosly)
/// 2. The CDC becomes unready at the src side in the next cycle after
///    synchronous reset request until the reset sequence is completed. A currently
///    pending transactions might still complete (if the dst accepts at the
///    exact time the reset is request on the src die).
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
/* verilator lint_off DECLFILENAME */

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module cc_cdc_2phase_clearable #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 3,
  parameter bit ClearOnAsyncReset = 1
)(
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
  // Asynchronous payload handshake signals between the source and destination.
  (* dont_touch = "true" *) logic async_payload_req;
  (* dont_touch = "true" *) logic async_payload_ack;
  (* dont_touch = "true" *) data_t async_payload_data;

  // Asynchronous clear-controller phase handshakes between the domains.
  (* dont_touch = "true" *) logic async_reset_src2dst_req;
  (* dont_touch = "true" *) logic async_reset_dst2src_ack;
  (* dont_touch = "true" *) cc_pkg::cdc_clear_seq_phase_e async_reset_src2dst_next_phase;
  (* dont_touch = "true" *) logic async_reset_dst2src_req;
  (* dont_touch = "true" *) logic async_reset_src2dst_ack;
  (* dont_touch = "true" *) cc_pkg::cdc_clear_seq_phase_e async_reset_dst2src_next_phase;

  // Clear/isolate contract:
  // - src/dst_clear_pending_o are the local isolate requests.
  // - local isolate and clear acknowledgements are one-cycle delayed copies of
  //   the corresponding local requests.
  // - isolate gates the external valid/ready interface on both sides.
  // - transactions accepted before or during a clear sequence may complete or
  //   be dropped, but fresh post-clear traffic must not be duplicated,
  //   reordered, or corrupted.

  if (ClearOnAsyncReset) begin : gen_elaboration_assertion
    if (SyncStages < 3)
      $error("The clearable 2-phase CDC with async reset",
             "synchronization requires at least 3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_elaboration_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end


  // The source-domain wrapper owns the payload CDC half, local clear/isolate
  // acknowledgements, and the local reset-controller half.
  cc_cdc_2phase_src_domain_clearable #(
    .data_t            ( data_t            ),
    .SyncStages        ( SyncStages        ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_src_domain (
    .src_rst_ni                ( src_rst_ni                     ),
    .src_clk_i                 ( src_clk_i                      ),
    .src_clear_i               ( src_clear_i                    ),
    .src_clear_pending_o       ( src_clear_pending_o            ),
    .src_data_i                ( src_data_i                     ),
    .src_valid_i               ( src_valid_i                    ),
    .src_ready_o               ( src_ready_o                    ),
    (* async *) .async_payload_req_o  ( async_payload_req  ),
    (* async *) .async_payload_ack_i  ( async_payload_ack  ),
    (* async *) .async_payload_data_o ( async_payload_data ),
    (* async *) .async_reset_next_phase_o ( async_reset_src2dst_next_phase ),
    (* async *) .async_reset_req_o        ( async_reset_src2dst_req        ),
    (* async *) .async_reset_ack_i        ( async_reset_dst2src_ack        ),
    (* async *) .async_reset_next_phase_i ( async_reset_dst2src_next_phase ),
    (* async *) .async_reset_req_i        ( async_reset_dst2src_req        ),
    (* async *) .async_reset_ack_o        ( async_reset_src2dst_ack        )
  );


  // The destination-domain wrapper owns the payload CDC half, local
  // clear/isolate acknowledgements, and the local reset-controller half.
  cc_cdc_2phase_dst_domain_clearable #(
    .data_t            ( data_t            ),
    .SyncStages        ( SyncStages        ),
    .ClearOnAsyncReset ( ClearOnAsyncReset )
  ) i_dst_domain (
    .dst_rst_ni                ( dst_rst_ni                     ),
    .dst_clk_i                 ( dst_clk_i                      ),
    .dst_clear_i               ( dst_clear_i                    ),
    .dst_clear_pending_o       ( dst_clear_pending_o            ),
    .dst_data_o                ( dst_data_o                     ),
    .dst_valid_o               ( dst_valid_o                    ),
    .dst_ready_i               ( dst_ready_i                    ),
    (* async *) .async_payload_req_i  ( async_payload_req  ),
    (* async *) .async_payload_ack_o  ( async_payload_ack  ),
    (* async *) .async_payload_data_i ( async_payload_data ),
    (* async *) .async_reset_next_phase_o ( async_reset_dst2src_next_phase ),
    (* async *) .async_reset_req_o        ( async_reset_dst2src_req        ),
    (* async *) .async_reset_ack_i        ( async_reset_src2dst_ack        ),
    (* async *) .async_reset_next_phase_i ( async_reset_src2dst_next_phase ),
    (* async *) .async_reset_req_i        ( async_reset_src2dst_req        ),
    (* async *) .async_reset_ack_o        ( async_reset_dst2src_ack        )
  );

`ifndef COMMON_CELLS_ASSERTS_OFF

  `ASSERT(no_valid_i_during_clear_i, src_clear_i |-> !src_valid_i, src_clk_i, !src_rst_ni)

`endif

endmodule


/// Destination-domain wrapper for the clearable two-phase CDC.
module cc_cdc_2phase_dst_domain_clearable #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2,
  parameter bit ClearOnAsyncReset = 1
) (
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  output logic dst_clear_pending_o,
  output data_t dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i,
  input  logic async_payload_req_i,
  output logic async_payload_ack_o,
  input  data_t async_payload_data_i,
  output cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_o,
  output logic async_reset_req_o,
  input  logic async_reset_ack_i,
  input  cc_pkg::cdc_clear_seq_phase_e async_reset_next_phase_i,
  input  logic async_reset_req_i,
  output logic async_reset_ack_o
);

  logic dst_clear_req;
  logic dst_clear_ack_q;
  logic dst_isolate_req;
  logic dst_isolate_ack_q;
  logic dst_valid;

  if (ClearOnAsyncReset) begin : gen_elaboration_assertion
    if (SyncStages < 3)
      $error("The clearable 2-phase CDC with async reset",
             "synchronization requires at least 3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_sync_stage_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  // Keep the clear-control path one synchronizer stage ahead of the payload CDC
  // when async reset propagation is enabled, but never below two stages.
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

  cc_cdc_2phase_dst_clearable #(
    .data_t     ( data_t     ),
    .SyncStages ( SyncStages )
  ) i_dst (
    .rst_ni       ( dst_rst_ni                         ),
    .clk_i        ( dst_clk_i                          ),
    .clear_i      ( dst_clear_req                      ),
    .data_o       ( dst_data_o                         ),
    .valid_o      ( dst_valid                          ),
    .ready_i      ( dst_ready_i & !dst_isolate_req     ),
    (* async *) .async_req_i  ( async_payload_req_i  ),
    (* async *) .async_ack_o  ( async_payload_ack_o  ),
    (* async *) .async_data_i ( async_payload_data_i )
  );

  assign dst_valid_o = dst_valid & !dst_isolate_req;

  // Isolation and clear are acknowledged one cycle after the local request.
  `FF(dst_isolate_ack_q, dst_isolate_req, 1'b0, dst_clk_i, dst_rst_ni)
  `FF(dst_clear_ack_q,   dst_clear_req,   1'b0, dst_clk_i, dst_rst_ni)

  assign dst_clear_pending_o = dst_isolate_req;

endmodule


/// Source-domain wrapper for the clearable two-phase CDC.
module cc_cdc_2phase_src_domain_clearable #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2,
  parameter bit ClearOnAsyncReset = 1
) (
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  output logic src_clear_pending_o,
  input  data_t src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  output logic async_payload_req_o,
  input  logic async_payload_ack_i,
  output data_t async_payload_data_o,
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
      $error("The clearable 2-phase CDC with async reset",
             "synchronization requires at least 3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SyncStages < 2) begin : gen_sync_stage_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  // Keep the clear-control path one synchronizer stage ahead of the payload CDC
  // when async reset propagation is enabled, but never below two stages.
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

  cc_cdc_2phase_src_clearable #(
    .data_t     ( data_t     ),
    .SyncStages ( SyncStages )
  ) i_src (
    .rst_ni       ( src_rst_ni                         ),
    .clk_i        ( src_clk_i                          ),
    .clear_i      ( src_clear_req                      ),
    .data_i       ( src_data_i                         ),
    .valid_i      ( src_valid_i & !src_isolate_req     ),
    .ready_o      ( src_ready                          ),
    (* async *) .async_req_o  ( async_payload_req_o  ),
    (* async *) .async_ack_i  ( async_payload_ack_i  ),
    (* async *) .async_data_o ( async_payload_data_o )
  );

  assign src_ready_o = src_ready & !src_isolate_req;

  // Isolation and clear are acknowledged one cycle after the local request.
  `FF(src_isolate_ack_q, src_isolate_req, 1'b0, src_clk_i, src_rst_ni)
  `FF(src_clear_ack_q,   src_clear_req,   1'b0, src_clk_i, src_rst_ni)

  assign src_clear_pending_o = src_isolate_req; // The isolate signal stays
                                                // asserted during the whole
                                                // clear sequence.

endmodule


/// Half of the two-phase clock domain crossing located in the source domain.
module cc_cdc_2phase_src_clearable #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2
) (
  input  logic  rst_ni,
  input  logic  clk_i,
  input  logic  clear_i,
  input  data_t data_i,
  input  logic  valid_i,
  output logic  ready_o,
  output logic  async_req_o,
  input  logic  async_ack_i,
  output data_t async_data_o
);

  (* dont_touch = "true" *)
  logic  req_src_d, req_src_q, ack_synced;
  (* dont_touch = "true" *)
  data_t data_src_d, data_src_q;

  // Synchronize the async ACK
  tc_sync #(
    .Stages(SyncStages)
  ) i_sync(
    .clk_i,
    .rst_ni,
    .serial_i( async_ack_i ),
    .serial_o( ack_synced  )
  );

  // If we receive the clear signal clear the content of the request flip-flop
  // and the data register
  always_comb begin
    data_src_d = data_src_q;
    req_src_d  = req_src_q;
    if (clear_i) begin
      req_src_d  = 1'b0;
    // The req_src and data_src registers change when a new data item is accepted.
    end else if (valid_i && ready_o) begin
      req_src_d  = ~req_src_q;
      data_src_d = data_i;
    end
  end

  `FFNR(data_src_q, data_src_d, clk_i)

  `FF(req_src_q, req_src_d, 1'b0, clk_i, rst_ni)

  // Output assignments.
  assign ready_o = (req_src_q == ack_synced);
  assign async_req_o = req_src_q;
  assign async_data_o = data_src_q;

// Assertions
`ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSUME(no_clear_and_request, clear_i |-> ~valid_i, clk_i, !rst_ni,
          "No request allowed while clear_i is asserted.")
`endif

endmodule


/// Half of the two-phase clock domain crossing located in the destination
/// domain.
module cc_cdc_2phase_dst_clearable #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2
)(
  input  logic  rst_ni,
  input  logic  clk_i,
  input  logic  clear_i,
  output data_t data_o,
  output logic  valid_o,
  input  logic  ready_i,
  input  logic  async_req_i,
  output logic  async_ack_o,
  input  data_t async_data_i
);

  (* dont_touch = "true" *)
  (* async_reg = "true" *)
  logic  ack_dst_d, ack_dst_q, req_synced, req_synced_q1;
  (* dont_touch = "true" *)
  data_t data_dst_d, data_dst_q;


  //Synchronize the request
  tc_sync #(
    .Stages(SyncStages)
  ) i_sync(
    .clk_i,
    .rst_ni,
    .serial_i( async_req_i ),
    .serial_o( req_synced  )
  );

  // The ack_dst register changes when a new data item is accepted.
  always_comb begin
    ack_dst_d = ack_dst_q;
    if (clear_i) begin
      ack_dst_d = 1'b0;
    end else if (valid_o && ready_i) begin
      ack_dst_d = ~ack_dst_q;
    end
  end

  // The data_dst register samples when a new data item is presented. This is
  // indicated by a transition in the req_synced line.
  always_comb begin
    data_dst_d = data_dst_q;
    if (req_synced != req_synced_q1 && !valid_o) begin
      data_dst_d = async_data_i;
    end
  end

  `FFNR(data_dst_q, data_dst_d, clk_i)

  `FF(ack_dst_q, ack_dst_d, 1'b0, clk_i, rst_ni)
  // The req_synced_q1 is the delayed version of the synchronized req_synced
  // used to detect transitions in the request.
  `FF(req_synced_q1, req_synced, 1'b0, clk_i, rst_ni)

  // Output assignments.
  assign valid_o = (ack_dst_q != req_synced_q1);
  assign data_o = data_dst_q;
  assign async_ack_o = ack_dst_q;

endmodule
/* verilator lint_on DECLFILENAME */
