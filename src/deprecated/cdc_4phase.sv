// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cdc_4phase instead.
module cdc_4phase #(
  parameter type         T              = logic,
  parameter int unsigned SYNC_STAGES    = 2,
  parameter bit          DECOUPLED      = 1'b1,
  parameter bit          SEND_RESET_MSG = 1'b0,
  parameter T            RESET_MSG      = T'('0)
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
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_4phase' instead.");
  // synthesis translate_on
  cc_cdc_4phase #(
    .data_t       ( T              ),
    .SyncStages   ( SYNC_STAGES    ),
    .Decoupled    ( DECOUPLED      ),
    .SendResetMsg ( SEND_RESET_MSG ),
    .ResetMsg     ( RESET_MSG      )
  ) i_cc_cdc_4phase (
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

// Deprecated: use cc_cdc_4phase_src instead.
module cdc_4phase_src #(
  parameter type         T             = logic,
  parameter int unsigned SYNC_STAGES   = 2,
  parameter bit          DECOUPLED     = 1'b1,
  parameter bit          SEND_RESET_MSG = 1'b0,
  parameter T            RESET_MSG     = T'('0)
)(
  input  logic rst_ni,
  input  logic clk_i,
  input  T     data_i,
  input  logic valid_i,
  output logic ready_o,
  output logic async_req_o,
  input  logic async_ack_i,
  output T     async_data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_4phase_src' instead.");
  // synthesis translate_on
  cc_cdc_4phase_src #(
    .data_t ( T             ),
    .SyncStages    ( SYNC_STAGES   ),
    .Decoupled ( DECOUPLED     ),
    .SendResetMsg ( SEND_RESET_MSG),
    .ResetMsg ( RESET_MSG     )
  ) i_cc_cdc_4phase_src (
    .rst_ni       ( rst_ni       ),
    .clk_i        ( clk_i        ),
    .data_i       ( data_i       ),
    .valid_i      ( valid_i      ),
    .ready_o      ( ready_o      ),
    .async_req_o  ( async_req_o  ),
    .async_ack_i  ( async_ack_i  ),
    .async_data_o ( async_data_o )
  );
endmodule

// Deprecated: use cc_cdc_4phase_dst instead.
module cdc_4phase_dst #(
  parameter type         T           = logic,
  parameter int unsigned SYNC_STAGES = 2,
  parameter bit          DECOUPLED   = 1
)(
  input  logic rst_ni,
  input  logic clk_i,
  output T     data_o,
  output logic valid_o,
  input  logic ready_i,
  input  logic async_req_i,
  output logic async_ack_o,
  input  T     async_data_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cdc_4phase_dst' instead.");
  // synthesis translate_on
  cc_cdc_4phase_dst #(
    .data_t ( T           ),
    .SyncStages  ( SYNC_STAGES ),
    .Decoupled ( DECOUPLED   )
  ) i_cc_cdc_4phase_dst (
    .rst_ni       ( rst_ni       ),
    .clk_i        ( clk_i        ),
    .data_o       ( data_o       ),
    .valid_o      ( valid_o      ),
    .ready_i      ( ready_i      ),
    .async_req_i  ( async_req_i  ),
    .async_ack_o  ( async_ack_o  ),
    .async_data_i ( async_data_i )
  );
endmodule
