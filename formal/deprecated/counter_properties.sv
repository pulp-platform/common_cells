// Copyright 2019 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_counter_properties instead.

module counter_properties #(
    parameter int unsigned WIDTH = 4,
    parameter bit STICKY_OVERFLOW = 1'b0
)(
    input logic             clk_i,
    input logic             rst_ni,
    input logic             clear_i,
    input logic             en_i,
    input logic             load_i,
    input logic             down_i,
    input logic [WIDTH-1:0] d_i,
    input logic [WIDTH-1:0] q_o,
    input logic             overflow_o
);
  cc_counter_properties #(
    .WIDTH           ( WIDTH           ),
    .STICKY_OVERFLOW ( STICKY_OVERFLOW )
  ) i_cc_counter_properties (
    .clk_i      ( clk_i                               ),
    .rst_ni     ( rst_ni                              ),
    .clr_i      ( clear_i                             ),
    .en_i       ( en_i                                ),
    .load_i     ( load_i                              ),
    .down_i     ( down_i                              ),
    .delta_i    ( {{WIDTH-1{1'b0}}, 1'b1}             ),
    .d_i        ( d_i                                 ),
    .q_o        ( q_o                                 ),
    .overflow_o ( overflow_o                          )
  );
endmodule

bind counter counter_properties #(
    .WIDTH(WIDTH), .STICKY_OVERFLOW(STICKY_OVERFLOW)
) i_counter_properties(.*);
