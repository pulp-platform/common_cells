// Regular VT
// CKXOR2M1RA, CKXOR2M2RA, CKXOR2M4RA
// CKXOR2M8RA, CKXOR2M12RA

// Low VT
// CKXOR2M1WA, CKXOR2M2WA, CKXOR2M4WA
// CKXOR2M8WA, CKXOR2M12WA

// High VT
// CKXOR2M1SA, CKXOR2M2SA, CKXOR2M4SA
// CKXOR2M8SA, CKXOR2M12SA

module cluster_clock_xor2
(
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
);

`ifdef USE_SC8
   CLKXOR2_X12_A8TL clk_xor_i 
   (
      .Y(clk_o),
      .A(clk0_i),
      .B(clk1_i) 
   );
`endif

`ifdef USE_SC9
   XOR2_X1P4M_A9TL clk_xor_i 
   (
      .Y(clk_o),
      .A(clk0_i),
      .B(clk1_i) 
   );
`endif


`ifdef USE_SC12
   XOR2_X1P4M_A12TL clk_xor_i 
   (
      .Y(clk_o),
      .A(clk0_i),
      .B(clk1_i) 
   );
`endif



endmodule
