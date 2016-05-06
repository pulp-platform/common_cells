
module pulp_clock_mux2
  (
   input  logic clk0_i,
   input  logic clk1_i,
   input  logic clk_sel_i,
   output logic clk_o
   );
   
  BUFGMUX bufgmux_i (
    .S(clk_sel_i),
    .I0(clk0_i),
    .I1(clk1_i),
    .O(clk_o)
  );
   
endmodule
