
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

  PREICG_X2B_A7TR_C34 clk_gate_i
  (
    .ECK ( clk_o     ),
    .CK  ( clk_i     ),
    .E   ( en_i      ),
    .SE  ( test_en_i )
  );

endmodule
