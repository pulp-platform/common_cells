// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>
//
// This module can be used to generate any mask that can be obtained
// by a boxcar function (https://en.wikipedia.org/wiki/Boxcar_function).
// Specifically, it generates a mask with all and only the bits in
// the (lsb_i, msb_i] interval asserted.

module boxcar #(
    parameter int unsigned Width = 32,
    /// Derived parameter *Do not override*
    localparam int unsigned IdxWidth = cf_math_pkg::idx_width(Width),
    localparam type idx_t = logic [IdxWidth-1:0],
    localparam type mask_t = logic [Width-1:0]
) (
    input idx_t lsb_i,
    input idx_t msb_i,
    output mask_t mask_o
);

    mask_t low_mask, high_mask_n;

    heaviside #(.Width(Width)) i_lo (.x_i(lsb_i), .mask_o(low_mask));
    heaviside #(.Width(Width)) i_hi (.x_i(msb_i), .mask_o(high_mask_n));

    assign mask_o = ~low_mask & high_mask_n;

endmodule
