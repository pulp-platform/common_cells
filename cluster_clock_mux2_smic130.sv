module clock_mux2
  (
   input  logic clk_in0,
   input  logic clk_in1,
   input  logic clk_select,
   output logic clk_out
   );
 
`ifndef HVT_only
   MUX2CLKHD2X clk_mux_i
     (
	    .A(clk_in0),
	    .B(clk_in1),
	    .S0(clk_select),
	    .Z(clk_out)
	    );
`else
   MUX2CLKHD2XHT clk_mux_i
     (
	    .A(clk_in0),
	    .B(clk_in1),
	    .S0(clk_select),
	    .Z(clk_out)
	    );
`endif
   
endmodule
