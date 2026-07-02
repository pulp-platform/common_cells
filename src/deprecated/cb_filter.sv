// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_cb_filter instead.
// Note: Seeds parameter type changed from cb_filter_pkg::cb_seed_t to cc_pkg::cb_seed_t,
// and the default changed from cb_filter_pkg::EgSeeds to cc_pkg::CbEgSeeds.
module cb_filter #(
  parameter int unsigned KHashes     =  32'd3,
  parameter int unsigned HashWidth   =  32'd4,
  parameter int unsigned HashRounds  =  32'd1,
  parameter int unsigned InpWidth    =  32'd32,
  parameter int unsigned BucketWidth =  32'd4,
  parameter cc_pkg::cb_seed_t [KHashes-1:0] Seeds = cc_pkg::CbEgSeeds
)(
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic [InpWidth-1:0]  look_data_i,
  output logic                 look_valid_o,
  input  logic [InpWidth-1:0]  incr_data_i,
  input  logic                 incr_valid_i,
  input  logic [InpWidth-1:0]  decr_data_i,
  input  logic                 decr_valid_i,
  input  logic                 filter_clear_i,
  output logic [HashWidth-1:0] filter_usage_o,
  output logic                 filter_full_o,
  output logic                 filter_empty_o,
  output logic                 filter_error_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_cb_filter' instead.");
  // synthesis translate_on
  cc_cb_filter #(
    .KHashes     ( KHashes     ),
    .HashWidth   ( HashWidth   ),
    .HashRounds  ( HashRounds  ),
    .InpWidth    ( InpWidth    ),
    .BucketWidth ( BucketWidth ),
    .Seeds       ( Seeds       )
  ) i_cc_cb_filter (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .clr_i          ( filter_clear_i ),
    .look_data_i    ( look_data_i    ),
    .look_valid_o   ( look_valid_o   ),
    .incr_data_i    ( incr_data_i    ),
    .incr_valid_i   ( incr_valid_i   ),
    .decr_data_i    ( decr_data_i    ),
    .decr_valid_i   ( decr_valid_i   ),
    .filter_usage_o ( filter_usage_o ),
    .filter_full_o  ( filter_full_o  ),
    .filter_empty_o ( filter_empty_o ),
    .filter_error_o ( filter_error_o )
  );
endmodule
