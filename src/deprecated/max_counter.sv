// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_max_counter instead.

module max_counter #(
  parameter int unsigned WIDTH = 4
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             clear_i,
  input  logic             clear_max_i,
  input  logic             en_i,
  input  logic             load_i,
  input  logic             down_i,
  input  logic [WIDTH-1:0] delta_i,
  input  logic [WIDTH-1:0] d_i,
  output logic [WIDTH-1:0] q_o,
  output logic [WIDTH-1:0] max_o,
  output logic             overflow_o,
  output logic             overflow_max_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_max_counter' instead.");
  // synthesis translate_on
  cc_max_counter #(
    .Width ( WIDTH )
  ) i_cc_max_counter (
    .clk_i         ( clk_i         ),
    .rst_ni        ( rst_ni        ),
    .clr_i      ( clear_i       ),
    .clr_cnt_i  ( 1'b0          ),
    .clr_max_i  ( clear_max_i   ),
    .en_i          ( en_i          ),
    .load_i        ( load_i        ),
    .down_i        ( down_i        ),
    .delta_i       ( delta_i       ),
    .d_i           ( d_i           ),
    .q_o           ( q_o           ),
    .max_o         ( max_o         ),
    .overflow_o    ( overflow_o    ),
    .overflow_max_o( overflow_max_o)
  );
endmodule
