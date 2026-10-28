// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_popcount instead.

module popcount #(
  parameter int unsigned INPUT_WIDTH = 256
) (
  input  logic [INPUT_WIDTH-1:0]              data_i,
  output logic [$clog2(INPUT_WIDTH):0]        popcount_o
);
  // cc_popcount counts into $clog2(INPUT_WIDTH+1) bits, one fewer than this 1.x port when
  // INPUT_WIDTH is not a power of two: count at its width, then zero-extend into the port.
  localparam int unsigned PopcountWidth = $clog2(INPUT_WIDTH+1);
  logic [PopcountWidth-1:0] popcount;

  // synthesis translate_off
  `ifndef COMMON_CELLS_NO_DEPRECATED_WARNINGS
  initial $warning("Module '%m' is deprecated. Use 'cc_popcount' instead.");
  `endif
  // synthesis translate_on
  cc_popcount #(
    .InputWidth ( INPUT_WIDTH )
  ) i_cc_popcount (
    .data_i     ( data_i     ),
    .popcount_o ( popcount   )
  );
  assign popcount_o = ($clog2(INPUT_WIDTH)+1)'(popcount);
endmodule
