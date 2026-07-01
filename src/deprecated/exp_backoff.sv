// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_exp_backoff instead.

module exp_backoff #(
  parameter int unsigned Seed   = 'hffff,
  parameter int unsigned MaxExp = 16
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic set_i,
  input  logic clr_i,
  output logic is_zero_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_exp_backoff' instead.");
  // synthesis translate_on
  cc_exp_backoff #(
    .Seed   ( Seed   ),
    .MaxExp ( MaxExp )
  ) i_cc_exp_backoff (
    .clk_i     ( clk_i     ),
    .rst_ni    ( rst_ni    ),
    .clr_i     ( 1'b0     ),
    .set_cnt_i ( set_i     ),
    .clr_cnt_i ( clr_i ),
    .is_zero_o ( is_zero_o )
  );
endmodule
