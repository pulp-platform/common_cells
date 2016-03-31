module pulp_clock_inverter
  (
   input  logic clk_i,
   output logic clk_o
   );

`ifndef HVT_only   
   INVCLKHD2X clk_buf_i
     (
		  .A(clk_i),
		  .Z(clk_o)
		  );
`else
   INVCLKHD2XHT clk_buf_i
     (
		  .A(clk_i),
		  .Z(clk_o)
		  );
`endif
   
endmodule
