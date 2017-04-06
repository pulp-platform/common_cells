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

module cluster_clock_mux2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   input  logic clk_sel_i,
   output logic clk_o
   );
 
`ifndef HVT_only
   MUX2CLKHD2X clk_mux_i
     (
	    .A(clk0_i),
	    .B(clk1_i),
	    .S0(clk_sel_i),
	    .Z(clk_o)
	    );
`else
   MUX2CLKHD2XHT clk_mux_i
     (
	    .A(clk0_i),
	    .B(clk1_i),
	    .S0(clk_sel_i),
	    .Z(clk_o)
	    );
`endif
   
endmodule
