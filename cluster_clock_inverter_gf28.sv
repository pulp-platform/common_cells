
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
`define GF_INV(t,v,c)  INV_X2B_A``t``T``v``_C``c

module cluster_clock_inverter
(
    input  logic clk_i,
    output logic clk_o
  );

  `GF_INV(`GF_TRACK, `GF_VT, `GF_LEN) clk_inv_i
  (
    .A ( clk_i ),
    .Y ( clk_o )
  );

endmodule
