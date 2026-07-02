// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_boxcar instead.

module boxcar #(
  parameter int unsigned Width = 32
) (
  input  logic [cc_pkg::idx_width(Width)-1:0] lsb_i,
  input  logic [cc_pkg::idx_width(Width)-1:0] msb_i,
  output logic [Width-1:0]                          mask_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_boxcar' instead.");
  // synthesis translate_on
  cc_boxcar #(
    .Width ( Width )
  ) i_cc_boxcar (
    .lsb_i  ( lsb_i  ),
    .msb_i  ( msb_i  ),
    .mask_o ( mask_o )
  );
endmodule
