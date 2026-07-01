// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_lzc instead.
// Note: parameter MODE type changed from bit to cc_pkg::lzc_mode_e in the new module.
// The default changed from 1'b0 (trailing zeros) to LZC_LEADING_ZERO_CNT.
// This wrapper preserves the old default of 1'b0 (trailing zeros).
module lzc #(
  parameter int unsigned WIDTH     = 2,
  parameter bit          MODE      = 1'b0,
  parameter int unsigned CNT_WIDTH = cc_pkg::idx_width(WIDTH)
)(
  input  logic [WIDTH-1:0]     in_i,
  output logic [CNT_WIDTH-1:0] cnt_o,
  output logic                 empty_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_lzc' instead.");
  // synthesis translate_on
  localparam cc_pkg::lzc_mode_e CC_MODE = MODE ? cc_pkg::LZC_LEADING_ZERO_CNT : cc_pkg::LZC_TRAILING_ZERO_CNT;
  cc_lzc #(
    .Width ( WIDTH   ),
    .Mode ( CC_MODE )
  ) i_cc_lzc (
    .in_i    ( in_i    ),
    .cnt_o   ( cnt_o   ),
    .empty_o ( empty_o )
  );
endmodule
