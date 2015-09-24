
// MXGL2
// 2-to-1 glitchless multiplexer

module cluster_clock_mux2
(
    input  logic clk0_i,
    input  logic clk1_i,
    input  logic clk_sel_i,
    output logic clk_o
  );

  MXGL2_X2B_A7TR_C34 clk_mux_i
  (
    .A  ( clk0_i    ),
    .B  ( clk1_i    ),
    .S0 ( clk_sel_i ),
    .Y  ( clk_o     )
  );

endmodule
