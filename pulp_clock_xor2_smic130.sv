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

module pulp_clock_xor2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
   );

`ifndef HVT_only
   XOR2CLKHD2X clk_xor_i
     (
		  .Z(clk_o),
		  .A(clk0_i),
		  .B(clk1_i)
		  );
`else
   XOR2CLKHD2XHT clk_xor_i
     (
		  .Z(clk_o),
		  .A(clk0_i),
		  .B(clk1_i)
		  );
`endif
   
endmodule
