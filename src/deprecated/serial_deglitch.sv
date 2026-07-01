// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_serial_deglitch instead.

module serial_deglitch #(
  parameter int unsigned SIZE = 4
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic en_i,
  input  logic d_i,
  output logic q_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_serial_deglitch' instead.");
  // synthesis translate_on
  cc_serial_deglitch #(
    .Threshold ( SIZE )
  ) i_cc_serial_deglitch (
    .clk_i   ( clk_i  ),
    .rst_ni  ( rst_ni ),
    .clr_i   ( 1'b0   ),
    .restart_i ( 1'b0   ),
    .en_i    ( en_i   ),
    .d_i     ( d_i    ),
    .q_o     ( q_o    )
  );
endmodule
