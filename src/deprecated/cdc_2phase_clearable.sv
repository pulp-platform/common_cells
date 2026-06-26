// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_2phase_clearable instead.
module cdc_2phase_clearable #(
  parameter type         T                  = logic,
  parameter int unsigned SYNC_STAGES        = 3,
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
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_2phase_clearable' instead.");
  // synthesis translate_on
  cc_cdc_2phase_clearable #(
    .T                   ( T                   ),
    .SYNC_STAGES         ( SYNC_STAGES         ),
    .CLEAR_ON_ASYNC_RESET( CLEAR_ON_ASYNC_RESET)
  ) i_cc_cdc_2phase_clearable (
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

// Deprecated: use cc_cdc_2phase_src_clearable instead.
module cdc_2phase_src_clearable #(
  parameter type         T           = logic,
  parameter int unsigned SYNC_STAGES = 2
)(
  input  logic rst_ni,
  input  logic clk_i,
  input  logic clear_i,
  input  T     data_i,
  input  logic valid_i,
  output logic ready_o,
  output logic async_req_o,
  input  logic async_ack_i,
  output T     async_data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_2phase_src_clearable' instead.");
  // synthesis translate_on
  cc_cdc_2phase_src_clearable #(
    .T           ( T           ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_cc_cdc_2phase_src_clearable (
    .rst_ni       ( rst_ni       ),
    .clk_i        ( clk_i        ),
    .clear_i      ( clear_i      ),
    .data_i       ( data_i       ),
    .valid_i      ( valid_i      ),
    .ready_o      ( ready_o      ),
    .async_req_o  ( async_req_o  ),
    .async_ack_i  ( async_ack_i  ),
    .async_data_o ( async_data_o )
  );
endmodule

// Deprecated: use cc_cdc_2phase_dst_clearable instead.
module cdc_2phase_dst_clearable #(
  parameter type         T           = logic,
  parameter int unsigned SYNC_STAGES = 2
)(
  input  logic rst_ni,
  input  logic clk_i,
  input  logic clear_i,
  output T     data_o,
  output logic valid_o,
  input  logic ready_i,
  input  logic async_req_i,
  output logic async_ack_o,
  input  T     async_data_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_2phase_dst_clearable' instead.");
  // synthesis translate_on
  cc_cdc_2phase_dst_clearable #(
    .T           ( T           ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_cc_cdc_2phase_dst_clearable (
    .rst_ni       ( rst_ni       ),
    .clk_i        ( clk_i        ),
    .clear_i      ( clear_i      ),
    .data_o       ( data_o       ),
    .valid_o      ( valid_o      ),
    .ready_i      ( ready_i      ),
    .async_req_i  ( async_req_i  ),
    .async_ack_o  ( async_ack_o  ),
    .async_data_i ( async_data_i )
  );
endmodule
