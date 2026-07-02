// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_fifo_optimal_wrap instead.
module stream_fifo_optimal_wrap #(
    parameter int unsigned Depth     = 32'd8,
    parameter type         type_t    = logic,
    parameter bit          PrintInfo = 1'b0,
    parameter int unsigned AddrDepth = (Depth > 32'd1) ? $clog2(Depth) : 32'd1
)(
    input  logic                 clk_i,
    input  logic                 rst_ni,
    input  logic                 flush_i,
    input  logic                 testmode_i,
    output logic [AddrDepth-1:0] usage_o,
    input  type_t                data_i,
    input  logic                 valid_i,
    output logic                 ready_o,
    output type_t                data_o,
    output logic                 valid_o,
    input  logic                 ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_fifo_optimal_wrap' instead.");
  // synthesis translate_on
  logic [cc_pkg::cnt_width(Depth)-1:0] usage;
  assign usage_o = usage[AddrDepth-1:0];
  cc_stream_fifo_optimal_wrap #(
    .Depth     ( Depth     ),
    .data_t ( type_t    ),
    .PrintInfo ( PrintInfo )
  ) i_cc_stream_fifo_optimal_wrap (
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
