// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_gray_to_binary instead.

module gray_to_binary #(
  parameter int N = 1
) (
  input  logic [N-1:0] A,
  output logic [N-1:0] Z
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_gray_to_binary' instead.");
  // synthesis translate_on
  cc_gray_to_binary #(
    .Width ( N )
  ) i_cc_gray_to_binary (
    .a_i ( A ),
    .z_o ( Z )
  );
endmodule
