// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_plru_tree instead.

module plru_tree #(
  parameter int unsigned ENTRIES = 16
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic [ENTRIES-1:0] used_i,
  output logic [ENTRIES-1:0] plru_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_plru_tree' instead.");
  // synthesis translate_on
  cc_plru_tree #(
    .ENTRIES ( ENTRIES )
  ) i_cc_plru_tree (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .used_i ( used_i ),
    .plru_o ( plru_o )
  );
endmodule
