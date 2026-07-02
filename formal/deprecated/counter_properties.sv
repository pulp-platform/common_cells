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
  ) i_cc_counter_properties (.*);
endmodule

bind counter counter_properties #(
    .WIDTH(WIDTH), .STICKY_OVERFLOW(STICKY_OVERFLOW)
) i_counter_properties(.*);
