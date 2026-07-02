// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_fifo_gray instead.
module cdc_fifo_gray #(
  parameter int unsigned WIDTH      = 1,
  parameter type         T          = logic [WIDTH-1:0],
  parameter int          LOG_DEPTH  = 3,
  parameter int          SYNC_STAGES = 2
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
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray #(
    .Width ( WIDTH       ),
    .data_t ( T           ),
    .LogDepth ( LOG_DEPTH   ),
    .SyncStages ( SYNC_STAGES )
  ) i_cc_cdc_fifo_gray (
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

// Deprecated: use cc_cdc_fifo_gray_src instead.
module cdc_fifo_gray_src #(
  parameter type T          = logic,
  parameter int  LOG_DEPTH  = 3,
  parameter int  SYNC_STAGES = 2
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  output T [2**LOG_DEPTH-1:0] async_data_o,
  output logic [LOG_DEPTH:0]  async_wptr_o,
  input  logic [LOG_DEPTH:0]  async_rptr_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray_src' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray_src #(
    .data_t ( T           ),
    .LogDepth ( LOG_DEPTH   ),
    .SyncStages ( SYNC_STAGES )
  ) i_cc_cdc_fifo_gray_src (
    .src_rst_ni   ( src_rst_ni   ),
    .src_clk_i    ( src_clk_i    ),
    .src_data_i   ( src_data_i   ),
    .src_valid_i  ( src_valid_i  ),
    .src_ready_o  ( src_ready_o  ),
    .async_data_o ( async_data_o ),
    .async_wptr_o ( async_wptr_o ),
    .async_rptr_i ( async_rptr_i )
  );
endmodule

// Deprecated: use cc_cdc_fifo_gray_dst instead.
module cdc_fifo_gray_dst #(
  parameter type T          = logic,
  parameter int  LOG_DEPTH  = 3,
  parameter int  SYNC_STAGES = 2
)(
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i,
  input  T [2**LOG_DEPTH-1:0] async_data_i,
  input  logic [LOG_DEPTH:0]  async_wptr_i,
  output logic [LOG_DEPTH:0]  async_rptr_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray_dst' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray_dst #(
    .data_t ( T           ),
    .LogDepth ( LOG_DEPTH   ),
    .SyncStages ( SYNC_STAGES )
  ) i_cc_cdc_fifo_gray_dst (
    .dst_rst_ni   ( dst_rst_ni   ),
    .dst_clk_i    ( dst_clk_i    ),
    .dst_data_o   ( dst_data_o   ),
    .dst_valid_o  ( dst_valid_o  ),
    .dst_ready_i  ( dst_ready_i  ),
    .async_data_i ( async_data_i ),
    .async_wptr_i ( async_wptr_i ),
    .async_rptr_o ( async_rptr_o )
  );
endmodule
