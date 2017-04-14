module pulp_clock_mux2
(
   input  logic clk0_i,
   input  logic clk1_i,
   input  logic clk_sel_i,
   output logic clk_o
);

   MX2_X4B_A9TR50 clk_mux_i
   (
      .A(clk0_i),
      .B(clk1_i),
      .S0(clk_sel_i),
      .Y(clk_o)
   );

endmodule
