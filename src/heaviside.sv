// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>
//
// This module can be used to generate any mask that can be obtained by the
// Heaviside function (https://en.wikipedia.org/wiki/Heaviside_step_function).
// Specifically, it generates a mask with all and only the bits in
// the [0, x_i] interval asserted.

module heaviside #(
    parameter int unsigned Width = 32,
    /// Derived parameter *Do not override*
    localparam int unsigned IdxWidth = cf_math_pkg::idx_width(Width),
    localparam type idx_t = logic [IdxWidth-1:0],
    localparam type mask_t = logic [Width-1:0]
) (
    input idx_t x_i,
    output mask_t mask_o
);

    assign mask_o = (1 << (x_i + 1)) - 1;

endmodule
