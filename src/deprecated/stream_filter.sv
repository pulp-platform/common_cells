// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_filter instead.

module stream_filter (
  input  logic valid_i,
  output logic ready_o,
  input  logic drop_i,
  output logic valid_o,
  input  logic ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_filter' instead.");
  // synthesis translate_on
  cc_stream_filter i_cc_stream_filter (
    .valid_i ( valid_i ),
    .ready_o ( ready_o ),
    .drop_i  ( drop_i  ),
    .valid_o ( valid_o ),
    .ready_i ( ready_i )
  );
endmodule
