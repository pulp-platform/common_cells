module pulp_clock_mux2
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
