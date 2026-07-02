// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_counter instead.

module counter #(
  parameter int unsigned WIDTH           = 4,
  parameter bit          STICKY_OVERFLOW = 1'b0
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             clear_i,
  input  logic             en_i,
  input  logic             load_i,
  input  logic             down_i,
  input  logic [WIDTH-1:0] d_i,
  output logic [WIDTH-1:0] q_o,
  output logic             overflow_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_counter' instead.");
  // synthesis translate_on
  cc_counter #(
    .Width ( WIDTH           ),
    .StickyOverflow ( STICKY_OVERFLOW )
  ) i_cc_counter (
    .clk_i      ( clk_i      ),
    .rst_ni     ( rst_ni     ),
    .clr_i      ( clear_i    ),
    .en_i       ( en_i       ),
    .load_i     ( load_i     ),
    .down_i     ( down_i     ),
    .d_i        ( d_i        ),
    .q_o        ( q_o        ),
    .overflow_o ( overflow_o )
  );
endmodule
