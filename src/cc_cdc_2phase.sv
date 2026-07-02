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

/// A two-phase clock domain crossing.
///
/// # Reset Behavior!!
///
/// This module must not be used if warm reset capabily is a requirement. The
/// only execption is if you consistently use a reset controller that sequences
/// the resets while gating both clock domains (be very careful if you follow
/// this strategy!). If you need warm reset/clear/flush capabilities, use (AND
/// CAREFULLY READ THE DESCRIPTION) the cc_cdc_2phase_clearable module.
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
/// the paths async_req, async_ack, async_data.
`include "common_cells/registers.svh"

module cc_cdc_2phase #(
  parameter type data_t = logic,
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

  // Asynchronous handshake signals.
  (* dont_touch = "true" *) logic  async_req;
  (* dont_touch = "true" *) logic  async_ack;
  (* dont_touch = "true" *) data_t async_data;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  // The sender in the source domain.
  cc_cdc_2phase_src #(
    .data_t     ( data_t     ),
    .SyncStages ( SyncStages )
  ) i_src (
    .rst_ni       ( src_rst_ni  ),
    .clk_i        ( src_clk_i   ),
    .data_i       ( src_data_i  ),
    .valid_i      ( src_valid_i ),
    .ready_o      ( src_ready_o ),
    .async_req_o  ( async_req   ),
    .async_ack_i  ( async_ack   ),
    .async_data_o ( async_data  )
  );

  // The receiver in the destination domain.
  cc_cdc_2phase_dst #(
    .data_t     ( data_t     ),
    .SyncStages ( SyncStages )
  ) i_dst (
    .rst_ni       ( dst_rst_ni  ),
    .clk_i        ( dst_clk_i   ),
    .data_o       ( dst_data_o  ),
    .valid_o      ( dst_valid_o ),
    .ready_i      ( dst_ready_i ),
    .async_req_i  ( async_req   ),
    .async_ack_o  ( async_ack   ),
    .async_data_i ( async_data  )
  );

endmodule


/// Half of the two-phase clock domain crossing located in the source domain.
module cc_cdc_2phase_src #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2
)(
  input  logic  rst_ni,
  input  logic  clk_i,
  input  data_t data_i,
  input  logic  valid_i,
  output logic  ready_o,
  output logic  async_req_o,
  input  logic  async_ack_i,
  output data_t async_data_o
);

  (* dont_touch = "true" *)
  logic req_src_q, ack_synced;
  (* dont_touch = "true" *)
  data_t data_src_q;
  logic src_accept;

  assign src_accept = valid_i && ready_o;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  // Synchronize the async ACK.
  tc_sync #(
    .Stages ( SyncStages )
  ) i_sync (
    .clk_i,
    .rst_ni,
    .serial_i ( async_ack_i ),
    .serial_o ( ack_synced  )
  );

  // The req_src and data_src registers change when a new data item is accepted.
  `FFL(req_src_q,  ~req_src_q, src_accept, 1'b0,       clk_i, rst_ni)
  `FFL(data_src_q, data_i,     src_accept, data_t'('0), clk_i, rst_ni)

  // Output assignments.
  assign ready_o = (req_src_q == ack_synced);
  assign async_req_o = req_src_q;
  assign async_data_o = data_src_q;

endmodule


/// Half of the two-phase clock domain crossing located in the destination
/// domain.
module cc_cdc_2phase_dst #(
  parameter type data_t = logic,
  parameter int unsigned SyncStages = 2
)(
  input  logic  rst_ni,
  input  logic  clk_i,
  output data_t data_o,
  output logic  valid_o,
  input  logic  ready_i,
  input  logic  async_req_i,
  output logic  async_ack_o,
  input  data_t async_data_i
);

  (* dont_touch = "true" *)
  logic req_synced, req_synced_q1, ack_dst_q;
  (* dont_touch = "true" *)
  data_t data_dst_q;
  logic dst_accept, dst_data_load;

  assign dst_accept   = valid_o && ready_i;
  assign dst_data_load = req_synced != req_synced_q1 && !valid_o;

  if (SyncStages < 2) begin : gen_sync_stage_assertion
    $error("A minimum of 2 synchronizer stages is required for proper functionality.");
  end

  // Synchronize the async request.
  tc_sync #(
    .Stages ( SyncStages )
  ) i_sync (
    .clk_i,
    .rst_ni,
    .serial_i ( async_req_i ),
    .serial_o ( req_synced  )
  );

  // The ack_dst register changes when a new data item is accepted.
  `FFL(ack_dst_q, ~ack_dst_q, dst_accept, 1'b0, clk_i, rst_ni)

  // The data_dst register changes when a new data item is presented. This is
  // indicated by the async_req line changing levels.
  `FFL(data_dst_q, async_data_i, dst_data_load, data_t'('0), clk_i, rst_ni)

  // Delayed version of the synchronized request for transition detection.
  `FF(req_synced_q1, req_synced, 1'b0, clk_i, rst_ni)

  // Output assignments.
  assign valid_o = (ack_dst_q != req_synced_q1);
  assign data_o = data_dst_q;
  assign async_ack_o = ack_dst_q;

endmodule
