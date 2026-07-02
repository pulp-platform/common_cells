// Copyright 2019 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_fall_through_register_properties instead.
// Note: testmode_i is accepted for port compatibility but not forwarded — it was
// never referenced in the property body.

module fall_through_register_properties #(
    parameter type T = logic
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic clr_i,
    input  logic testmode_i,
    input  logic valid_i,
    input  logic ready_o,
    input  T     data_i,
    input  logic valid_o,
    input  logic ready_i,
    input  T     data_o
);
  cc_fall_through_register_properties #(
    .T ( T )
  ) i_cc_fall_through_register_properties (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .clr_i   ( clr_i   ),
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .data_i  ( data_i  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i ),
    .data_o  ( data_o  )
  );
endmodule

bind fall_through_register fall_through_register_properties #(
    .T(T)
) i_fall_through_register_properties(.*);
