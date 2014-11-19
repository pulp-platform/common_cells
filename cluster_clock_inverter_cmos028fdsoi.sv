// C12T28SOI_LL_CNIVX16_P0
// C12T28SOI_LL_CNIVX16_P4
// C12T28SOI_LL_CNIVX16_P10
// C12T28SOI_LL_CNIVX16_P16
// C12T32_LLUP10_CNIVX16

module cluster_clock_inverter
  (
   input  logic clk_i,
   output logic clk_o
   );
   
   C12T32_LLUP10_CNIVX16
     clk_buf_i (
		.A(clk_i),
		.Z(clk_o)
		);
   
endmodule
