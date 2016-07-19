
// Regular VT
// CKMUX2M2R, CKMUX2M3R, CKMUX2M4R
// CKMUX2M6R, CKMUX2M8R
// CKMUX2M12R, CKMUX2M16RA

// Low VT
// CKMUX2M2W, CKMUX2M3W, CKMUX2M4W
// CKMUX2M6W, CKMUX2M8W
// CKMUX2M12W, CKMUX2M16WA

// High VT
// CKMUX2M2S, CKMUX2M3S, CKMUX2M4S
// CKMUX2M6S, CKMUX2M8S
// CKMUX2M12S, CKMUX2M16SA


module cluster_clock_mux2
(
   input  logic clk0_i,
   input  logic clk1_i,
   input  logic clk_sel_i,
   output logic clk_o
);

`ifdef USE_SC8
   CLKMX2_X12_A8TL clk_mux_i
   (
      .A(clk0_i),
      .B(clk1_i),
      .S0(clk_sel_i),
      .Y(clk_o)
   );
`endif

`ifdef USE_SC9
   MX2_X1P4M_A9TL clk_mux_i
   (
      .A(clk0_i),
      .B(clk1_i),
      .S0(clk_sel_i),
      .Y(clk_o)
   );
`endif

`ifdef USE_SC12
   MX2_X1P4M_A12TL clk_mux_i
   (
      .A(clk0_i),
      .B(clk1_i),
      .S0(clk_sel_i),
      .Y(clk_o)
   );
`endif

endmodule
