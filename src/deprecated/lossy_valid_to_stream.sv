// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_lossy_valid_to_stream instead.

module lossy_valid_to_stream #(
  parameter int unsigned DATA_WIDTH = 32,
  parameter type         T          = logic [DATA_WIDTH-1:0]
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic valid_i,
  input  T     data_i,
  output logic valid_o,
  input  logic ready_i,
  output T     data_o,
  output logic busy_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_lossy_valid_to_stream' instead.");
  // synthesis translate_on
  cc_lossy_valid_to_stream #(
    .DATA_WIDTH ( DATA_WIDTH ),
    .T          ( T          )
  ) i_cc_lossy_valid_to_stream (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .valid_i ( valid_i ),
    .data_i  ( data_i  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i ),
    .data_o  ( data_o  ),
    .busy_o  ( busy_o  )
  );
endmodule
