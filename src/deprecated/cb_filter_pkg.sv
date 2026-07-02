// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use 'cc_pkg' instead. This package forwards to 'cc_pkg' so that
// designs still referencing 'cb_filter_pkg::*' continue to elaborate.

package cb_filter_pkg;

  typedef cc_pkg::cb_seed_t cb_seed_t;

  localparam cb_seed_t [2:0] EgSeeds = cc_pkg::CbEgSeeds;

endpackage
