// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use 'cc_pkg' instead. This package forwards to 'cc_pkg' so that
// designs still referencing 'cdc_reset_ctrlr_pkg::*' continue to elaborate.

package cdc_reset_ctrlr_pkg;

  // Re-declare with the old member names, encoding-compatible with cc_pkg::cdc_clear_seq_phase_e.
  typedef enum logic[1:0] {
    CLEAR_PHASE_IDLE       = cc_pkg::CDC_CLEAR_PHASE_IDLE,
    CLEAR_PHASE_ISOLATE    = cc_pkg::CDC_CLEAR_PHASE_ISOLATE,
    CLEAR_PHASE_CLEAR      = cc_pkg::CDC_CLEAR_PHASE_CLEAR,
    CLEAR_PHASE_POST_CLEAR = cc_pkg::CDC_CLEAR_PHASE_POST_CLEAR
  } clear_seq_phase_e;

endpackage : cdc_reset_ctrlr_pkg
