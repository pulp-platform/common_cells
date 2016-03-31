module pulp_clock_buffer
  (
   input  logic clk_i,
   output logic clk_o
   );

`ifndef HVT_only   
   BUFCLKHD4X clk_buf_i 
     (
		  .A(clk_i),
		  .Z(clk_o)
		  );
`else 
   BUFCLKHD4XHT clk_buf_i 
     (
		  .A(clk_i),
		  .Z(clk_o)
		  );
`endif
   
endmodule
