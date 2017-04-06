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
// LAGCEPM2R, LAGCEPM3R, LAGCEPM4R
// LAGCEPM6R, LAGCEPM8R
// LAGCEPM12R, LAGCEPM16R
// LAGCEPM20R

// Low VT
// LAGCEPM2W, LAGCEPM3W, LAGCEPM4W
// LAGCEPM6W, LAGCEPM8W
// LAGCEPM12W, LAGCEPM16W
// LAGCEPM20W

// High VT
// LAGCEPM2S, LAGCEPM3S, LAGCEPM4S
// LAGCEPM6S, LAGCEPM8S
// LAGCEPM12S, LAGCEPM16S
// LAGCEPM20S

`include "ulpsoc_defines.sv"

module pulp_clock_gating
(
    input  logic clk_i,
    input  logic en_i,
    input  logic test_en_i,
    output logic clk_o
);

    LAGCEPM12R clk_gate_i 
    (
        .GCK(clk_o),
        .CK(clk_i),
        .E(en_i),
        .SE(test_en_i)
    );

endmodule
