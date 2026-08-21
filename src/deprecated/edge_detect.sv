// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_edge_detect instead.

module edge_detect (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic d_i,
  output logic re_o,
  output logic fe_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_edge_detect' instead.");
  // synthesis translate_on
  cc_edge_detect i_cc_edge_detect (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .d_i    ( d_i    ),
    .re_o   ( re_o   ),
    .fe_o   ( fe_o   )
  );
endmodule
