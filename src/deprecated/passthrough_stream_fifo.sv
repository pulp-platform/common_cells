// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_passthrough_stream_fifo instead.

module passthrough_stream_fifo #(
  parameter int unsigned Depth       = 32'd8,
  parameter bit          PrintInfo   = 1'b0,
  parameter bit          SameCycleRW = 1'b1,
  parameter type         type_t      = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  flush_i,
  input  logic  testmode_i,
  input  type_t data_i,
  input  logic  valid_i,
  output logic  ready_o,
  output type_t data_o,
  output logic  valid_o,
  input  logic  ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_passthrough_stream_fifo' instead.");
  // synthesis translate_on
  cc_passthrough_stream_fifo #(
    .Depth       ( Depth       ),
    .PrintInfo   ( PrintInfo   ),
    .SameCycleRW ( SameCycleRW ),
    .data_t ( type_t      )
  ) i_cc_passthrough_stream_fifo (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .clr_i   ( 1'b0   ),
    .flush_i ( flush_i ),
    .data_i  ( data_i  ),
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .data_o  ( data_o  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i )
  );
endmodule
