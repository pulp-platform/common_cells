// Available cells:
// C12T28SOI_LL_CNMUX21X17_P0;
// C12T28SOI_LL_CNMUX21X17_P4;
// C12T28SOI_LL_CNMUX21X17_P10;
// C12T28SOI_LL_CNMUX21X17_P16;

// C12T28SOI_LL_CNMUX21X33_P0;
// C12T28SOI_LL_CNMUX21X33_P4;
// C12T28SOI_LL_CNMUX21X33_P10;
// C12T28SOI_LL_CNMUX21X33_P16;
//
// 12T UWVR
// C12T32_LLUP10_CNMUX21X17;
//
// 8T RVT
// C8T28SOI_LR_CNMUX21X15_P0
// C8T28SOI_LR_CNMUX21X15_P4
// C8T28SOI_LR_CNMUX21X15_P10
// C8T28SOI_LR_CNMUX21X15_P16

module cluster_clock_mux2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   input  logic clk_sel_i,
   output logic clk_o
   );
   
   C8T28SOI_LR_CNMUX21X15_P0
     clk_mux_i
       (
	.D0(clk0_i),
	.D1(clk1_i),
	.S0(clk_sel_i),
	.Z(clk_o)
	);
   
endmodule
