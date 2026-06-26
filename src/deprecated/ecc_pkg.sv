// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use 'cc_pkg' instead. This package forwards to 'cc_pkg' so that
// designs still referencing 'ecc_pkg::*' continue to elaborate.

package ecc_pkg;

  function automatic int unsigned get_parity_width (input int unsigned data_width);
    // synopsys translate_off
    $warning("Package 'ecc_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::ecc_get_parity_width(data_width);
  endfunction

  function automatic int unsigned get_cw_width (input int unsigned data_width);
    // synopsys translate_off
    $warning("Package 'ecc_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::ecc_get_cw_width(data_width);
  endfunction

endpackage
