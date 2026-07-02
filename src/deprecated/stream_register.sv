// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_register instead.

module stream_register #(
  parameter type T = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clr_i,
  input  logic testmode_i,
  input  logic valid_i,
  output logic ready_o,
  input  T     data_i,
  output logic valid_o,
  input  logic ready_i,
  output T     data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_register' instead.");
  // synthesis translate_on
  cc_stream_register #(
    .data_t ( T )
  ) i_cc_stream_register (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .clr_i   ( clr_i   ),
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .data_i  ( data_i  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i ),
    .data_o  ( data_o  )
  );
endmodule
