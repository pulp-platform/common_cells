
module pulp_buffer
(
   input  logic in_i,
   output logic out_o
);

   BUF_X4B_A9TL  clk_buf_i
   (
      .A(in_i),
      .Y(out_o)
   );

endmodule
