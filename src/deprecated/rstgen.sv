// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_rstgen instead.

module rstgen (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic test_mode_i,
  output logic rst_no,
  output logic init_no
);
  // synthesis translate_off
  `ifndef COMMON_CELLS_NO_DEPRECATED_WARNINGS
  initial $warning("Module '%m' is deprecated. Use 'cc_rstgen' instead.");
  `endif
  // synthesis translate_on
  cc_rstgen i_cc_rstgen (
    .clk_i       ( clk_i       ),
    .rst_ni      ( rst_ni      ),
    .test_mode_i ( test_mode_i ),
    .rst_no      ( rst_no      ),
    .init_no     ( init_no     )
  );
endmodule
