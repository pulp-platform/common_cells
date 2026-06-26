// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_fifo_2phase instead.
module cdc_fifo_2phase #(
  parameter type T         = logic,
  parameter int  LOG_DEPTH = 3
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_2phase' instead.");
  // synthesis translate_on
  cc_cdc_fifo_2phase #(
    .T         ( T         ),
    .LOG_DEPTH ( LOG_DEPTH )
  ) i_cc_cdc_fifo_2phase (
    .src_rst_ni  ( src_rst_ni  ),
    .src_clk_i   ( src_clk_i   ),
    .src_data_i  ( src_data_i  ),
    .src_valid_i ( src_valid_i ),
    .src_ready_o ( src_ready_o ),
    .dst_rst_ni  ( dst_rst_ni  ),
    .dst_clk_i   ( dst_clk_i   ),
    .dst_data_o  ( dst_data_o  ),
    .dst_valid_o ( dst_valid_o ),
    .dst_ready_i ( dst_ready_i )
  );
endmodule
