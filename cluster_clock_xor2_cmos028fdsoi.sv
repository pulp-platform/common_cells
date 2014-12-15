// 12T UWVR
// C12T32_LLUAL4_CNHLSX7
// C12T32_LLUP0_XOR2X16

// 8T RVT
// C8T28SOI_LR_CNXOR2X15_P0
// C8T28SOI_LR_CNXOR2X15_P4
// C8T28SOI_LR_CNXOR2X15_P10
// C8T28SOI_LR_CNXOR2X15_P16

module cluster_clock_xor2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
   );
   
   C8T28SOI_LR_CNXOR2X15_P0 
     clk_xor_i (
		.Z(clk0_i),
		.A(clk1_i),
		.S(clk_o)  // --> 8T uses A,S as inputs, 12T uses A,B
		);
   
endmodule
