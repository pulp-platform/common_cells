// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_edge_propagator_tx instead.

module edge_propagator_tx (
  input  logic clk_i,
  input  logic rstn_i,
  input  logic valid_i,
  input  logic ack_i,
  output logic valid_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_edge_propagator_tx' instead.");
  // synthesis translate_on
  cc_edge_propagator_tx i_cc_edge_propagator_tx (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rstn_i  ),
    .valid_i ( valid_i ),
    .ack_i   ( ack_i   ),
    .valid_o ( valid_o )
  );
endmodule
