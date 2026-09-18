// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_read instead.

module read #(
  parameter int unsigned Width = 1,
  parameter type         T     = logic [Width-1:0]
) (
  input  T d_i,
  output T d_o
);
  // synthesis translate_off
  `ifndef COMMON_CELLS_NO_DEPRECATED_WARNINGS
  initial $warning("Module '%m' is deprecated. Use 'cc_read' instead.");
  `endif
  // synthesis translate_on
  cc_read #(
    .Width ( Width ),
    .data_t ( T     )
  ) i_cc_read (
    .d_i ( d_i ),
    .d_o ( d_o )
  );
endmodule
