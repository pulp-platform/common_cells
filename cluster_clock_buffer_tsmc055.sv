// Regular VT
// CKBUFM1R, CKBUFM2R, CKBUFM3R
// CKBUFM4R, CKBUFM6R
// CKBUFM8R, CKBUFM12R
// CKBUFM16R, CKBUFM20R
// CKBUFM22RA, CKBUFM24R
// CKBUFM26RA, CKBUFM32R
// CKBUFM40R, CKBUFM48R

// Low VT
// CKBUFM1W, CKBUFM2W, CKBUFM3W
// CKBUFM4W, CKBUFM6W
// CKBUFM8W, CKBUFM12W
// CKBUFM16W, CKBUFM20W
// CKBUFM22WA, CKBUFM24W
// CKBUFM26WA, CKBUFM32W
// CKBUFM40W, CKBUFM48W

// High VT
// CKBUFM1S, CKBUFM2S, CKBUFM3S
// CKBUFM4S, CKBUFM6S
// CKBUFM8S, CKBUFM12S
// CKBUFM16S, CKBUFM20S
// CKBUFM22SA, CKBUFM24S
// CKBUFM26SA, CKBUFM32S
// CKBUFM40S, CKBUFM48S

module cluster_clock_buffer
(
   input  logic clk_i,
   output logic clk_o
);

`ifdef USE_SC8
   CLKBUF_X24_A8TR clk_buf_i
   (
      .A(clk_i),
      .Y(clk_o)
   );
`endif

`ifdef USE_SC9
   BUF_X1P4M_A9TR clk_buf_i
   (
      .A(clk_i),
      .Y(clk_o)
   );
`endif


`ifdef USE_SC12
   BUF_X0P8M_A12TR clk_buf_i
   (
      .A(clk_i),
      .Y(clk_o)
   );
`endif



endmodule
