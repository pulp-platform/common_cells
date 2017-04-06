/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished 
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */

// Regular VT
// CKINVM1R, CKINVM2R, CKINVM3R
// CKINVM4R, CKINVM6R
// CKINVM8R, CKINVM12R
// CKINVM16R, CKINVM20R
// CKINVM22RA, CKINVM24R
// CKINVM26RA, CKINVM32R
// CKINVM40R, CKINVM48R

// Low VT
// CKINVM1W, CKINVM2W, CKINVM3W
// CKINVM4W, CKINVM6W
// CKINVM8W, CKINVM12W
// CKINVM16W, CKINVM20W
// CKINVM22WA, CKINVM24W
// CKINVM26WA, CKINVM32W
// CKINVM40W, CKINVM48W

// High VT
// CKINVM1S, CKINVM2S, CKINVM3S
// CKINVM4S, CKINVM6S
// CKINVM8S, CKINVM12S
// CKINVM16S, CKINVM20S
// CKINVM22SA, CKINVM24S
// CKINVM26SA, CKINVM32S
// CKINVM40S, CKINVM48S

module pulp_clock_inverter
(
    input  logic clk_i,
    output logic clk_o
);


    CKINVM22RA clk_inv_i 
    (
        .A(clk_i),
        .Z(clk_o)
    );

endmodule
