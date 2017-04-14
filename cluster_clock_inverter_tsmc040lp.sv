
module cluster_clock_inverter
(
   input  logic clk_i,
   output logic clk_o
);

    INV_X4B_A9TR50 clk_inv_i
    (
      .A(clk_i),
      .Y(clk_o)
    );

endmodule
