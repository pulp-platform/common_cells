// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_sync_wedge instead.

module sync_wedge #(
  parameter int unsigned STAGES = 2
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic en_i,
  input  logic serial_i,
  output logic r_edge_o,
  output logic f_edge_o,
  output logic serial_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_sync_wedge' instead.");
  // synthesis translate_on
  cc_sync_wedge #(
    .STAGES ( STAGES )
  ) i_cc_sync_wedge (
    .clk_i    ( clk_i    ),
    .rst_ni   ( rst_ni   ),
    .en_i     ( en_i     ),
    .serial_i ( serial_i ),
    .r_edge_o ( r_edge_o ),
    .f_edge_o ( f_edge_o ),
    .serial_o ( serial_o )
  );
endmodule
