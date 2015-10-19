
`ifndef GF_TRACK
  `define GF_TRACK  7
`endif

`ifndef GF_VT
  `define GF_VT     R
`endif

`ifndef GF_LEN
  `define GF_LEN   34
`endif

//andy hack: support different standard cell libraries by setting `GF_TRACK,
//`GF_VT and `GF_LEN
`define GF_BUF(t,v,c)  BUF_X3B_A``t``T``v``_C``c


module pulp_buffer
(
    input  logic in_i,
    output logic out_o
);

  `GF_BUF(`GF_TRACK, `GF_VT, `GF_LEN) buf_i
  (
    .A ( in_i  ),
    .Y ( out_o )
  );

endmodule
