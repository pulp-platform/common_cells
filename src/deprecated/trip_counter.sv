// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_trip_counter instead.

module trip_counter #(
  parameter int unsigned WIDTH = 4
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             en_i,
  input  logic [WIDTH-1:0] delta_i,
  input  logic [WIDTH-1:0] bound_i,
  output logic [WIDTH-1:0] q_o,
  output logic             last_o,
  output logic             trip_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_trip_counter' instead.");
  // synthesis translate_on
  cc_trip_counter #(
    .Width ( WIDTH )
  ) i_cc_trip_counter (
    .clk_i   ( clk_i  ),
    .rst_ni  ( rst_ni ),
    .clr_i  ( 1'b0  ),
    .en_i    ( en_i   ),
    .delta_i ( delta_i),
    .bound_i ( bound_i),
    .q_o     ( q_o    ),
    .last_o  ( last_o ),
    .trip_o  ( trip_o )
  );
endmodule
