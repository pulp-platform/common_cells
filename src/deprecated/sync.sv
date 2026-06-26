// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_sync instead.

module sync #(
  parameter int unsigned STAGES     = 2,
  parameter bit          ResetValue = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic serial_i,
  output logic serial_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_sync' instead.");
  // synthesis translate_on
  cc_sync #(
    .STAGES     ( STAGES     ),
    .ResetValue ( ResetValue )
  ) i_cc_sync (
    .clk_i    ( clk_i    ),
    .rst_ni   ( rst_ni   ),
    .serial_i ( serial_i ),
    .serial_o ( serial_o )
  );
endmodule
