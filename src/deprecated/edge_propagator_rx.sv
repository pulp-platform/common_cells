// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_edge_propagator_rx instead.

module edge_propagator_rx (
  input  logic clk_i,
  input  logic rstn_i,
  input  logic valid_i,
  output logic ack_o,
  output logic valid_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_edge_propagator_rx' instead.");
  // synthesis translate_on
  cc_edge_propagator_rx i_cc_edge_propagator_rx (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rstn_i  ),
    .valid_i ( valid_i ),
    .ack_o   ( ack_o   ),
    .valid_o ( valid_o )
  );
endmodule
