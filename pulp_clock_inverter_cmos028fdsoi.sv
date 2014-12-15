// C12T28SOI_LL_CNIVX16_P0
// C12T28SOI_LL_CNIVX16_P4
// C12T28SOI_LL_CNIVX16_P10
// C12T28SOI_LL_CNIVX16_P16
// C12T32_LLUP10_CNIVX16
//
// 12T UWVR
// C12T32_LLUP10_CNIVX16
//
// 8T RVT
// C8T28SOI_LR_CNIVX18_P0
// C8T28SOI_LR_CNIVX18_P4
// C8T28SOI_LR_CNIVX18_P10
// C8T28SOI_LR_CNIVX18_P16



module pulp_clock_inverter
(
   input  logic clk_i,
   output logic clk_o
);
   
   C8T28SOI_LR_CNIVX18_P0
     clk_buf_i (
		.A(clk_i),
		.Z(clk_o)
		);
   
endmodule
