// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>
//
// Contains common defintions for the LZC IP.

package lzc_pkg;

typedef enum logic {
  TRAILING_ZERO_CNT = 1'b0,
  LEADING_ZERO_CNT = 1'b1
} lzc_mode_e;

endpackage : lzc_pkg
