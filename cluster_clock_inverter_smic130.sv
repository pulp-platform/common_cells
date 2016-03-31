module clock_inverter
  (
   input  logic clk_in,
   output logic clk_out
   );

`ifndef HVT_only   
   INVCLKHD2X clk_buf_i
     (
		  .A(clk_in),
		  .Z(clk_out)
		  );
`else
   INVCLKHD2XHT clk_buf_i
     (
		  .A(clk_in),
		  .Z(clk_out)
		  );
`endif
   
endmodule
