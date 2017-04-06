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

// 12T UWVR
// C12T32_LLUAL4_CNHLSX7
// C12T32_LLUP0_XOR2X16

// 8T RVT
// C8T28SOI_LR_CNXOR2X15_P0
// C8T28SOI_LR_CNXOR2X15_P4
// C8T28SOI_LR_CNXOR2X15_P10
// C8T28SOI_LR_CNXOR2X15_P16

`include "ulpsoc_defines.sv"

module cluster_clock_xor2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
   );
   

`ifdef CMOS28FDSOI_8T
   C8T28SOI_LR_CNXOR2X15_P0 
     clk_xor_i (
		.Z(clk_o),
		.A(clk0_i),
		.S(clk1_i) // --> 8T uses A,S as inputs, 12T uses A,B
		);
`endif


`ifdef CMOS28FDSOI_12T_UWVR
   C12T32_LLUP0_XOR2X16 
     clk_xor_i (
		.Z(clk_o),
		.A(clk0_i),
		.B(clk1_i) // --> 8T uses A,S as inputs, 12T uses A,B
		);
`endif 
   
endmodule
