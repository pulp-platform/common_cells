
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
`define GF_PREICG(t,v,c)  PREICG_X2B_A``t``T``v``_C``c


// FRICG: no enable
// POSTICG: test over-ride input is asynchronous
// PREICG: test over-ride input is synchronous

module pulp_clock_gating
(
    input  logic clk_i,
    input  logic en_i,
    input  logic test_en_i,
    output logic clk_o
);

  `GF_PREICG(`GF_TRACK, `GF_VT, `GF_LEN) clk_gate_i
  (
    .ECK ( clk_o     ),
    .CK  ( clk_i     ),
    .E   ( en_i      ),
    .SE  ( test_en_i )
  );

endmodule
