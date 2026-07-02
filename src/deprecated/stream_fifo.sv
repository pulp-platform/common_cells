// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_fifo instead.

module stream_fifo #(
    parameter bit          FALL_THROUGH = 1'b0,
    parameter int unsigned DATA_WIDTH   = 32,
    parameter int unsigned DEPTH        = 8,
    parameter type         T            = logic [DATA_WIDTH-1:0],
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  flush_i,
    input  logic                  testmode_i,
    output logic [ADDR_DEPTH-1:0] usage_o,
    input  T                      data_i,
    input  logic                  valid_i,
    output logic                  ready_o,
    output T                      data_o,
    output logic                  valid_o,
    input  logic                  ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_fifo' instead.");
  // synthesis translate_on
  logic [cc_pkg::cnt_width(DEPTH)-1:0] usage;
  assign usage_o = usage[ADDR_DEPTH-1:0];
  cc_stream_fifo #(
    .FallThrough ( FALL_THROUGH ),
    .DataWidth ( DATA_WIDTH   ),
    .Depth ( DEPTH        ),
    .data_t       ( T            )
  ) i_cc_stream_fifo (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .clr_i   ( 1'b0   ),
    .flush_i ( flush_i ),
    .usage_o ( usage   ),
    .data_i  ( data_i  ),
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .data_o  ( data_o  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i )
  );
endmodule
