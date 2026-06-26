// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_sub_per_hash instead.

module sub_per_hash #(
  parameter int unsigned InpWidth    = 32'd11,
  parameter int unsigned HashWidth   = 32'd5,
  parameter int unsigned NoRounds    = 32'd1,
  parameter int unsigned PermuteKey  = 32'd299034753,
  parameter int unsigned XorKey      = 32'd4094834
) (
  input  logic [InpWidth-1:0]    data_i,
  output logic [HashWidth-1:0]   hash_o,
  output logic [2**HashWidth-1:0] hash_onehot_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_sub_per_hash' instead.");
  // synthesis translate_on
  cc_sub_per_hash #(
    .InpWidth   ( InpWidth   ),
    .HashWidth  ( HashWidth  ),
    .NoRounds   ( NoRounds   ),
    .PermuteKey ( PermuteKey ),
    .XorKey     ( XorKey     )
  ) i_cc_sub_per_hash (
    .data_i        ( data_i        ),
    .hash_o        ( hash_o        ),
    .hash_onehot_o ( hash_onehot_o )
  );
endmodule
