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

// C12T32_LLN2U4S_BFX16

`include "ulpsoc_defines.sv"

module pulp_level_shifter_in_clamp
(
    input  logic        in_i,
    output logic        out_o,
    input  logic        clamp_i
);



`ifdef CMOS28FDSOI_8T
    C8T28SOIDV_LRV_LSINCL0X32 lsin
    (
        .Z(out_o),
        .A(in_i),
        .R(clamp_i)
    );
`endif


`ifdef CMOS28FDSOI_12T_UWVR
    C12T32_LLN2U4S_BFX16  lsin
    (
        .Z(out_o),
        .A(in_i)
    );
`endif 


endmodule
