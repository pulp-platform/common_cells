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

// LL
// C12T28SOI_LL_CNBFX38_P0
// C12T28SOI_LL_CNBFX38_P4
// C12T28SOI_LL_CNBFX38_P10
// C12T28SOI_LL_CNBFX38_P16
// LR
// C12T28SOI_LR_CNBFX38_P0
// C12T28SOI_LR_CNBFX38_P4
// C12T28SOI_LR_CNBFX38_P10
// UWVR
// C12T32_LLUP10_CNBFX36
//
// 8T RVT
// C8T28SOI_LR_CNBFX37_P0
// C8T28SOI_LR_CNBFX37_P4
// C8T28SOI_LR_CNBFX37_P10
// C8T28SOI_LR_CNBFX37_P16

`include "ulpsoc_defines.sv"

module pulp_clock_buffer
(
    input  logic clk_i,
    output logic clk_o
);

`ifdef CMOS28FDSOI_8T
    C8T28SOI_LR_CNBFX37_P0  clk_buf_i
    (
        .A(clk_i),
        .Z(clk_o)
    );
`endif


`ifdef CMOS28FDSOI_12T_UWVR
    C12T32_LLUP10_CNBFX36 clk_buf_i
    (
        .A(clk_i),
        .Z(clk_o)
    );
`endif
endmodule
