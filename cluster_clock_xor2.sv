
module cluster_clock_xor2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
   );
   
   assign clk_o = clk0_1 ^ clk1_i;
   
endmodule
