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

module pulp_clock_gating
  (
   input  logic clk_i,
   input  logic en_i,
   input  logic test_en_i,
   output logic clk_o
   );
   
   C12T32_LLUAL4_CNHLSX7
     clk_gate_i (
		 .Q(clk_o),
		 .CP(clk_i),
		 .E(en_i),
		 .TE(test_en_i)
		 );
   
endmodule
