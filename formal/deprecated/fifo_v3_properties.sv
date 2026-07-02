// Copyright 2019 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_fifo_properties instead.
// Note: the deprecated fifo_v3 module now wraps cc_fifo. The properties checker
// relies on internal signals (read_pointer_n/q, write_pointer_n/q, status_cnt_n/q)
// that live inside the cc_fifo instance (i_cc_fifo), not in fifo_v3's scope.
// A module-level wrapper bound to fifo_v3 cannot reach those signals via .*,
// so this file instead binds cc_fifo_properties directly to the cc_fifo type,
// which covers i_cc_fifo inside every fifo_v3 instance automatically.
// testmode_i was accepted in the old port list but never used in any property.

bind cc_fifo cc_fifo_properties #(
    .FALL_THROUGH ( FALL_THROUGH ),
    .DATA_WIDTH   ( DATA_WIDTH   ),
    .DEPTH        ( DEPTH        )
) i_fifo_v3_properties(.*);
