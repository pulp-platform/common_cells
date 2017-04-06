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
// CKMUX2M2R, CKMUX2M3R, CKMUX2M4R
// CKMUX2M6R, CKMUX2M8R
// CKMUX2M12R, CKMUX2M16RA

// Low VT
// CKMUX2M2W, CKMUX2M3W, CKMUX2M4W
// CKMUX2M6W, CKMUX2M8W
// CKMUX2M12W, CKMUX2M16WA

// High VT
// CKMUX2M2S, CKMUX2M3S, CKMUX2M4S
// CKMUX2M6S, CKMUX2M8S
// CKMUX2M12S, CKMUX2M16SA


module pulp_clock_mux2
(
    input  logic clk0_i,
    input  logic clk1_i,
    input  logic clk_sel_i,
    output logic clk_o
);

    CKMUX2M12R clk_mux_i
    (
        .A(clk0_i),
        .B(clk1_i),
        .S(clk_sel_i),
        .Z(clk_o)
    );

endmodule
