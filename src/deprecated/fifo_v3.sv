// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_fifo instead.

module fifo_v3 #(
    parameter bit          FALL_THROUGH = 1'b0,
    parameter int unsigned DATA_WIDTH   = 32,
    parameter int unsigned DEPTH        = 8,
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  logic  clk_i,
    input  logic  rst_ni,
    input  logic  flush_i,
    input  logic  testmode_i,
    output logic  full_o,
    output logic  empty_o,
    output logic  [ADDR_DEPTH-1:0] usage_o,
    input  dtype  data_i,
    input  logic  push_i,
    output dtype  data_o,
    input  logic  pop_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_fifo' instead.");
  // synthesis translate_on
  cc_fifo #(
    .FALL_THROUGH ( FALL_THROUGH ),
    .DATA_WIDTH   ( DATA_WIDTH   ),
    .DEPTH        ( DEPTH        ),
    .dtype        ( dtype        )
  ) i_cc_fifo (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .flush_i ( flush_i ),
    .full_o  ( full_o  ),
    .empty_o ( empty_o ),
    .usage_o ( usage_o ),
    .data_i  ( data_i  ),
    .push_i  ( push_i  ),
    .data_o  ( data_o  ),
    .pop_i   ( pop_i   )
  );
endmodule
