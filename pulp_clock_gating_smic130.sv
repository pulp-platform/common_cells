module pulp_clock_gating
  (
   input  logic clk_i,
   input  logic en_i,
   input  logic test_en_i,
   output logic clk_o
   );

`ifndef HVT_only
   CLKGTOSHD2X clk_gate_i
     (
		  .Z(clk_o),
		  .CK(clk_i),
		  .E(en_i),
		  .TE(test_en_i),
		  .OBS()
		  );
`else
   CLKGTOSHD2XHT clk_gate_i
     (
		  .Z(clk_o),
		  .CK(clk_i),
		  .E(en_i),
		  .TE(test_en_i),
		  .OBS()
		  );
`endif
   
endmodule
