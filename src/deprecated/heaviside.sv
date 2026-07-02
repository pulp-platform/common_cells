// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_heaviside instead.

module heaviside #(
  parameter int unsigned Width = 32
) (
  input  logic [cc_pkg::idx_width(Width)-1:0] x_i,
  output logic [Width-1:0]                          mask_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_heaviside' instead.");
  // synthesis translate_on
  cc_heaviside #(
    .Width ( Width )
  ) i_cc_heaviside (
    .x_i    ( x_i    ),
    .mask_o ( mask_o )
  );
endmodule
