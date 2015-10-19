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
`define GF_XOR(t,v,c)  XOR2_X2M_A``t``T``v``_C``c

module pulp_clock_xor2
(
    input  logic clk0_i,
    input  logic clk1_i,
    output logic clk_o
  );

  `GF_XOR(`GF_TRACK, `GF_VT, `GF_LEN) clk_xor_i
  (
    .A ( clk0_i ),
    .B ( clk1_i ),
    .Y ( clk_o  )
  );

endmodule
