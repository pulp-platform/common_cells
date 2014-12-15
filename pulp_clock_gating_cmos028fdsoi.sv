// Available cells:
// LVT
// C12T28SOI_LLP_CNHLSX58_P0
// C12T28SOI_LLP_CNHLSX58_P4
// C12T28SOI_LLP_CNHLSX58_P10
// C12T28SOI_LLP_CNHLSX58_P16
// RVT
// C12T28SOI_LRP_CNHLSX58_P0
// C12T28SOI_LRP_CNHLSX58_P4
// C12T28SOI_LRP_CNHLSX58_P10
// C12T28SOI_LRP_CNHLSX58_P16
// UWVR
// C12T32_LLUAL4_CNHLSX7
//
//
//
// 8T RVT
// C8T28SOI_LRP_CNHLSX54_P0
// C8T28SOI_LRP_CNHLSX54_P4
// C8T28SOI_LRP_CNHLSX54_P10
// C8T28SOI_LRP_CNHLSX54_P16

module pulp_clock_gating
(
   input  logic clk_i,
   input  logic en_i,
   input  logic test_en_i,
   output logic clk_o
);


   C8T28SOI_LRP_CNHLSX54_P0
     clk_gate_i (
		 .Q(clk_o),
		 .CP(clk_i),
		 .E(en_i),
		 .TE(test_en_i)
		 );
   
endmodule
