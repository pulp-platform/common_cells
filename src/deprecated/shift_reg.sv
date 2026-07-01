// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_shift_register instead.

module shift_reg #(
  parameter type         dtype = logic,
  parameter int unsigned Depth = 1
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  dtype d_i,
  output dtype d_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_shift_register' instead.");
  // synthesis translate_on
  cc_shift_register #(
    .data_t ( dtype ),
    .Depth ( Depth )
  ) i_cc_shift_register (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .clr_i  ( 1'b0  ),
    .d_i    ( d_i    ),
    .d_o    ( d_o    )
  );
endmodule
