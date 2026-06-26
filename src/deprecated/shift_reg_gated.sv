// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_shift_register_gated instead.

module shift_reg_gated #(
  parameter int unsigned Depth = 32'd8,
  parameter type         dtype = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic valid_i,
  input  dtype data_i,
  output logic valid_o,
  output dtype data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_shift_register_gated' instead.");
  // synthesis translate_on
  cc_shift_register_gated #(
    .Depth  ( Depth  ),
    .dtype  ( dtype  )
  ) i_cc_shift_register_gated (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .valid_i ( valid_i ),
    .data_i  ( data_i  ),
    .valid_o ( valid_o ),
    .data_o  ( data_o  )
  );
endmodule
