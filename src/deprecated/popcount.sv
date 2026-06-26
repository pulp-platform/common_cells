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
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_popcount' instead.");
  // synthesis translate_on
  cc_popcount #(
    .INPUT_WIDTH ( INPUT_WIDTH )
  ) i_cc_popcount (
    .data_i     ( data_i     ),
    .popcount_o ( popcount_o )
  );
endmodule
