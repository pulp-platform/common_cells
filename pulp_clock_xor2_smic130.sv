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
