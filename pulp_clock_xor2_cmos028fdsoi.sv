// UWVR
// C12T32_LLUAL4_CNHLSX7

module pulp_clock_xor2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
   );
   
   C12T32_LLUP0_XOR2X16 
     clk_xor_i (
		.Z(clk_o),
		.A(clk0_i),
		.B(clk1_i)
		);
   
endmodule
