// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_clk_int_div_static instead.

module clk_int_div_static #(
  parameter int unsigned DIV_VALUE            = 1,
  parameter bit          ENABLE_CLOCK_IN_RESET = 1'b1
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic en_i,
  input  logic test_mode_en_i,
  output logic clk_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_clk_int_div_static' instead.");
  // synthesis translate_on
  cc_clk_int_div_static #(
    .DivValue ( DIV_VALUE             ),
    .EnableClockInReset ( ENABLE_CLOCK_IN_RESET )
  ) i_cc_clk_int_div_static (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .en_i           ( en_i           ),
    .test_mode_en_i ( test_mode_en_i ),
    .clk_o          ( clk_o          )
  );
endmodule
