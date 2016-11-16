module cluster_clock_buffer
(
   input  logic clk_i,
   output logic clk_o
);


   BUF_X4B_A9TL  clk_buf_i
   (
      .A(clk_i),
      .Y(clk_o)
   );

endmodule
