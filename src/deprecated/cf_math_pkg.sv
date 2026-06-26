// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use 'cc_pkg' instead. This package forwards to 'cc_pkg' so that
// designs still referencing 'cf_math_pkg::*' continue to elaborate.

package cf_math_pkg;

  function automatic integer ceil_div (input longint dividend, input longint divisor);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::ceil_div(dividend, divisor);
  endfunction

  function automatic integer unsigned idx_width (input integer unsigned num_idx);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::idx_width(num_idx);
  endfunction

  function automatic bit is_power_of_2 (input integer unsigned value);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::is_power_of_2(value);
  endfunction

  function automatic integer unsigned iomsb (input integer unsigned width);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::iomsb(width);
  endfunction

  function automatic int max (int a, int b);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::max(a, b);
  endfunction

  function automatic int min (int a, int b);
    // synopsys translate_off
    $warning("Package 'cf_math_pkg' is deprecated. Use 'cc_pkg' instead.");
    // synopsys translate_on
    return cc_pkg::min(a, b);
  endfunction

endpackage
