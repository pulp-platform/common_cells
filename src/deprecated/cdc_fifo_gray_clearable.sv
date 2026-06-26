// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_fifo_gray_clearable instead.
module cdc_fifo_gray_clearable #(
  parameter int unsigned WIDTH              = 1,
  parameter type         T                  = logic [WIDTH-1:0],
  parameter int          LOG_DEPTH          = 3,
  parameter int          SYNC_STAGES        = 3,
  parameter int          CLEAR_ON_ASYNC_RESET = 1
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  output logic src_clear_pending_o,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  output logic dst_clear_pending_o,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray_clearable' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray_clearable #(
    .WIDTH               ( WIDTH               ),
    .T                   ( T                   ),
    .LOG_DEPTH           ( LOG_DEPTH           ),
    .SYNC_STAGES         ( SYNC_STAGES         ),
    .CLEAR_ON_ASYNC_RESET( CLEAR_ON_ASYNC_RESET)
  ) i_cc_cdc_fifo_gray_clearable (
    .src_rst_ni          ( src_rst_ni          ),
    .src_clk_i           ( src_clk_i           ),
    .src_clear_i         ( src_clear_i         ),
    .src_clear_pending_o ( src_clear_pending_o ),
    .src_data_i          ( src_data_i          ),
    .src_valid_i         ( src_valid_i         ),
    .src_ready_o         ( src_ready_o         ),
    .dst_rst_ni          ( dst_rst_ni          ),
    .dst_clk_i           ( dst_clk_i           ),
    .dst_clear_i         ( dst_clear_i         ),
    .dst_clear_pending_o ( dst_clear_pending_o ),
    .dst_data_o          ( dst_data_o          ),
    .dst_valid_o         ( dst_valid_o         ),
    .dst_ready_i         ( dst_ready_i         )
  );
endmodule

// Deprecated: use cc_cdc_fifo_gray_src_clearable instead.
module cdc_fifo_gray_src_clearable #(
  parameter type T          = logic,
  parameter int  LOG_DEPTH  = 3,
  parameter int  SYNC_STAGES = 2
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,
  output T [2**LOG_DEPTH-1:0] async_data_o,
  output logic [LOG_DEPTH:0]  async_wptr_o,
  input  logic [LOG_DEPTH:0]  async_rptr_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray_src_clearable' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray_src_clearable #(
    .T           ( T           ),
    .LOG_DEPTH   ( LOG_DEPTH   ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_cc_cdc_fifo_gray_src_clearable (
    .src_rst_ni   ( src_rst_ni   ),
    .src_clk_i    ( src_clk_i    ),
    .src_clear_i  ( src_clear_i  ),
    .src_data_i   ( src_data_i   ),
    .src_valid_i  ( src_valid_i  ),
    .src_ready_o  ( src_ready_o  ),
    .async_data_o ( async_data_o ),
    .async_wptr_o ( async_wptr_o ),
    .async_rptr_i ( async_rptr_i )
  );
endmodule

// Deprecated: use cc_cdc_fifo_gray_dst_clearable instead.
module cdc_fifo_gray_dst_clearable #(
  parameter type T          = logic,
  parameter int  LOG_DEPTH  = 3,
  parameter int  SYNC_STAGES = 2
)(
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i,
  input  T [2**LOG_DEPTH-1:0] async_data_i,
  input  logic [LOG_DEPTH:0]  async_wptr_i,
  output logic [LOG_DEPTH:0]  async_rptr_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_fifo_gray_dst_clearable' instead.");
  // synthesis translate_on
  cc_cdc_fifo_gray_dst_clearable #(
    .T           ( T           ),
    .LOG_DEPTH   ( LOG_DEPTH   ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_cc_cdc_fifo_gray_dst_clearable (
    .dst_rst_ni   ( dst_rst_ni   ),
    .dst_clk_i    ( dst_clk_i    ),
    .dst_clear_i  ( dst_clear_i  ),
    .dst_data_o   ( dst_data_o   ),
    .dst_valid_o  ( dst_valid_o  ),
    .dst_ready_i  ( dst_ready_i  ),
    .async_data_i ( async_data_i ),
    .async_wptr_i ( async_wptr_i ),
    .async_rptr_o ( async_rptr_o )
  );
endmodule
