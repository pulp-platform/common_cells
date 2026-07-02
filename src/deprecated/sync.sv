// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use tc_sync from tech_cells_generic instead.

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
  initial $warning("Module '%m' is deprecated. Use 'tc_sync' from 'tech_cells_generic' instead.");
  // synthesis translate_on
  tc_sync #(
    .Stages     ( STAGES     ),
    .ResetValue ( ResetValue )
  ) i_tc_sync (
    .clk_i,
    .rst_ni,
    .serial_i,
    .serial_o
  );
endmodule
