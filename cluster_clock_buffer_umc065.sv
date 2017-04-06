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
// CKBUFM1R, CKBUFM2R, CKBUFM3R
// CKBUFM4R, CKBUFM6R
// CKBUFM8R, CKBUFM12R
// CKBUFM16R, CKBUFM20R
// CKBUFM22RA, CKBUFM24R
// CKBUFM26RA, CKBUFM32R
// CKBUFM40R, CKBUFM48R

// Low VT
// CKBUFM1W, CKBUFM2W, CKBUFM3W
// CKBUFM4W, CKBUFM6W
// CKBUFM8W, CKBUFM12W
// CKBUFM16W, CKBUFM20W
// CKBUFM22WA, CKBUFM24W
// CKBUFM26WA, CKBUFM32W
// CKBUFM40W, CKBUFM48W

// High VT
// CKBUFM1S, CKBUFM2S, CKBUFM3S
// CKBUFM4S, CKBUFM6S
// CKBUFM8S, CKBUFM12S
// CKBUFM16S, CKBUFM20S
// CKBUFM22SA, CKBUFM24S
// CKBUFM26SA, CKBUFM32S
// CKBUFM40S, CKBUFM48S

module cluster_clock_buffer
(
   input  logic clk_i,
   output logic clk_o
);

   CKBUFM22RA
     clk_buf_i (
		.A(clk_i),
		.Z(clk_o)
		);

endmodule
