// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_onehot_to_bin instead.

module onehot_to_bin #(
  parameter int unsigned ONEHOT_WIDTH = 16,
  // Derived parameter (kept for backward compatibility, do not override)
  parameter int unsigned BIN_WIDTH    = ONEHOT_WIDTH == 1 ? 1 : $clog2(ONEHOT_WIDTH)
) (
  input  logic [ONEHOT_WIDTH-1:0] onehot,
  output logic [BIN_WIDTH-1:0]    bin
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_onehot_to_bin' instead.");
  // synthesis translate_on
  // Note: BIN_WIDTH is a localparam in cc_onehot_to_bin, not passed.
  cc_onehot_to_bin #(
    .OnehotWidth ( ONEHOT_WIDTH )
  ) i_cc_onehot_to_bin (
    .onehot_i ( onehot ),
    .bin_o    ( bin    )
  );
endmodule
