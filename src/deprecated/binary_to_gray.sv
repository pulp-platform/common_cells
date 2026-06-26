// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_binary_to_gray instead.

module binary_to_gray #(
  parameter int N = -1
) (
  input  logic [N-1:0] A,
  output logic [N-1:0] Z
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_binary_to_gray' instead.");
  // synthesis translate_on
  cc_binary_to_gray #(
    .N ( N )
  ) i_cc_binary_to_gray (
    .A ( A ),
    .Z ( Z )
  );
endmodule
