// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_unread instead.

module unread (
  input logic d_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_unread' instead.");
  // synthesis translate_on
  cc_unread i_cc_unread (
    .d_i ( d_i )
  );
endmodule
