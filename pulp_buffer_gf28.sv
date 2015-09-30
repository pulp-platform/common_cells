
module pulp_buffer
(
    input  logic in_i,
    output logic out_o
);

  BUF_X3B_A7TR_C34 buf_i
  (
    .A ( in_i  ),
    .Y ( out_o )
  );

endmodule
