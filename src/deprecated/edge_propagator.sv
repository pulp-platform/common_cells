// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_edge_propagator instead.

module edge_propagator (
  input  logic clk_tx_i,
  input  logic rstn_tx_i,
  input  logic edge_i,
  input  logic clk_rx_i,
  input  logic rstn_rx_i,
  output logic edge_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_edge_propagator' instead.");
  // synthesis translate_on
  cc_edge_propagator i_cc_edge_propagator (
    .clk_tx_i  ( clk_tx_i  ),
    .rst_tx_ni ( rstn_tx_i ),
    .edge_i    ( edge_i    ),
    .clk_rx_i  ( clk_rx_i  ),
    .rst_rx_ni ( rstn_rx_i ),
    .edge_o    ( edge_o    )
  );
endmodule
