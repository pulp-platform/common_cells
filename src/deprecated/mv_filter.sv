// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_majority_vote_filter instead.
// Note: parameter WIDTH renamed to WINDOW_LEN, default THRESHOLD changed from 10 to
// (WINDOW_LEN/2)+1, and port sample_i renamed to en_i in the new module.
module mv_filter #(
    parameter int unsigned WIDTH     = 4,
    parameter int unsigned THRESHOLD = 10
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic sample_i,
    input  logic clear_i,
    input  logic d_i,
    output logic q_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_majority_vote_filter' instead.");
  // synthesis translate_on
  cc_majority_vote_filter #(
    .WindowLen ( WIDTH     ),
    .Threshold ( THRESHOLD )
  ) i_cc_majority_vote_filter (
    .clk_i   ( clk_i    ),
    .rst_ni  ( rst_ni   ),
    .clr_i   ( clear_i  ),
    .en_i    ( sample_i ),
    .d_i     ( d_i      ),
    .q_o     ( q_o      )
  );
endmodule
