// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_clk_int_div instead.

module clk_int_div #(
  parameter int unsigned DIV_VALUE_WIDTH      = 4,
  parameter int unsigned DEFAULT_DIV_VALUE    = 0,
  parameter bit          ENABLE_CLOCK_IN_RESET = 1'b0
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  input  logic                        en_i,
  input  logic                        test_mode_en_i,
  input  logic [DIV_VALUE_WIDTH-1:0]  div_i,
  input  logic                        div_valid_i,
  output logic                        div_ready_o,
  output logic                        clk_o,
  output logic [DIV_VALUE_WIDTH-1:0]  cycl_count_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_clk_int_div' instead.");
  // synthesis translate_on
  cc_clk_int_div #(
    .DIV_VALUE_WIDTH       ( DIV_VALUE_WIDTH       ),
    .DEFAULT_DIV_VALUE     ( DEFAULT_DIV_VALUE     ),
    .ENABLE_CLOCK_IN_RESET ( ENABLE_CLOCK_IN_RESET )
  ) i_cc_clk_int_div (
    .clk_i         ( clk_i         ),
    .rst_ni        ( rst_ni        ),
    .en_i          ( en_i          ),
    .test_mode_en_i( test_mode_en_i),
    .div_i         ( div_i         ),
    .div_valid_i   ( div_valid_i   ),
    .div_ready_o   ( div_ready_o   ),
    .clk_o         ( clk_o         ),
    .cycl_count_o  ( cycl_count_o  )
  );
endmodule
