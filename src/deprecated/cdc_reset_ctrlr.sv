// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_reset_ctrlr instead.
module cdc_reset_ctrlr #(
  parameter int unsigned SYNC_STAGES        = 2,
  parameter logic        CLEAR_ON_ASYNC_RESET = 1'b1
)(
  input  logic a_clk_i,
  input  logic a_rst_ni,
  input  logic a_clear_i,
  output logic a_clear_o,
  input  logic a_clear_ack_i,
  output logic a_isolate_o,
  input  logic a_isolate_ack_i,
  input  logic b_clk_i,
  input  logic b_rst_ni,
  input  logic b_clear_i,
  output logic b_clear_o,
  input  logic b_clear_ack_i,
  output logic b_isolate_o,
  input  logic b_isolate_ack_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_reset_ctrlr' instead.");
  // synthesis translate_on
  cc_cdc_reset_ctrlr #(
    .SyncStages ( SYNC_STAGES         ),
    .ClearOnAsyncReset ( CLEAR_ON_ASYNC_RESET)
  ) i_cc_cdc_reset_ctrlr (
    .a_clk_i          ( a_clk_i          ),
    .a_rst_ni         ( a_rst_ni         ),
    .a_clear_i        ( a_clear_i        ),
    .a_clear_o        ( a_clear_o        ),
    .a_clear_ack_i    ( a_clear_ack_i    ),
    .a_isolate_o      ( a_isolate_o      ),
    .a_isolate_ack_i  ( a_isolate_ack_i  ),
    .b_clk_i          ( b_clk_i          ),
    .b_rst_ni         ( b_rst_ni         ),
    .b_clear_i        ( b_clear_i        ),
    .b_clear_o        ( b_clear_o        ),
    .b_clear_ack_i    ( b_clear_ack_i    ),
    .b_isolate_o      ( b_isolate_o      ),
    .b_isolate_ack_i  ( b_isolate_ack_i  )
  );
endmodule

// Deprecated: use cc_cdc_reset_ctrlr_half instead.
// Note: async_next_phase ports use cc_pkg::cdc_clear_seq_phase_e (renamed from
// cdc_reset_ctrlr_pkg::clear_seq_phase_e).
module cdc_reset_ctrlr_half #(
  parameter int unsigned SYNC_STAGES        = 2,
  parameter logic        CLEAR_ON_ASYNC_RESET = 1'b1
)(
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          clear_i,
  output logic                          isolate_o,
  input  logic                          isolate_ack_i,
  output logic                          clear_o,
  input  logic                          clear_ack_i,
  output cc_pkg::cdc_clear_seq_phase_e  async_next_phase_o,
  output logic                          async_req_o,
  input  logic                          async_ack_i,
  input  cc_pkg::cdc_clear_seq_phase_e  async_next_phase_i,
  input  logic                          async_req_i,
  output logic                          async_ack_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_reset_ctrlr_half' instead.");
  // synthesis translate_on
  cc_cdc_reset_ctrlr_half #(
    .SyncStages ( SYNC_STAGES         ),
    .ClearOnAsyncReset ( CLEAR_ON_ASYNC_RESET)
  ) i_cc_cdc_reset_ctrlr_half (
    .clk_i              ( clk_i              ),
    .rst_ni             ( rst_ni             ),
    .clear_i            ( clear_i            ),
    .isolate_o          ( isolate_o          ),
    .isolate_ack_i      ( isolate_ack_i      ),
    .clear_o            ( clear_o            ),
    .clear_ack_i        ( clear_ack_i        ),
    .async_next_phase_o ( async_next_phase_o ),
    .async_req_o        ( async_req_o        ),
    .async_ack_i        ( async_ack_i        ),
    .async_next_phase_i ( async_next_phase_i ),
    .async_req_i        ( async_req_i        ),
    .async_ack_o        ( async_ack_o        )
  );
endmodule
