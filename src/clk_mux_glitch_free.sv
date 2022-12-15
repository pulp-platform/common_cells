//-----------------------------------------------------------------------------
// Title         : Glitch-free Clock Multiplexer
//-----------------------------------------------------------------------------
// File          : clk_mux_glitch_free.sv
// Author        : Manuel Eggimann  <meggimann@iis.ee.ethz.ch>
// Created       : 10.12.2022
//-----------------------------------------------------------------------------
// Description :
//
// This module allows glitch free clock multiplexing between N arbitrary input
// clock with completely unknown phase relation shipts. The module will make
// sure to first synchronize the clock multiplexer signal to the relevant clock
// domains and ensures glitch free switching between the source clock and the
// new target clock by silencing the output at appropriate times. The clock
// signals themselves only pass through: 1 clock-gate, 1 N-input clock-OR Gate,
// 1 2-input clock mux. All these cells are referenced from the tech_cells
// repository and thus no conventional logic gate is directly in the clock path.

// The correctness of this module is based on the following assumptions:
// 1. The select signal stays stable for a duration of at least min(clks_i
// period)
// 2. Glitches on the select signal are shorter than min(clks_i) - t_setup
// 3. During a transition from clock input a to clock input b, both clocks have
// a stable period.
//
// A clock switching procedure from clock a to clock b has the following timing behavior:
// 1. After at most NUM_SYNC_STAGES clock cycle of clock a, the output clock is
// disabled with its next falling edge.
// 2. After clock cycle of clock a and another NUM_SYNC_STAGES clock cycles of clock b, the output is
// enabled with the next rising edge of clock B.
//
// So in total, an upper bound for the worst case clock switching delay is 2x
// NUM_SYNC_STAGES x max(clock_periods)
//
//-----------------------------------------------------------------------------
// Copyright (C) 2013-2022 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//-----------------------------------------------------------------------------


module clk_mux_glitch_free #(
  parameter int unsigned  NUM_INPUTS = 2,
  parameter int unsigned NUM_SYNC_STAGES = 2,
  localparam int unsigned SelWidth = $clog2(NUM_INPUTS)
) (
   input logic [NUM_INPUTS-1:0] clks_i,
   input logic                  test_clk_i,
   input logic                  test_en_i,
   input logic                  async_rstn_i,
   input logic [SelWidth-1:0]   async_sel_i,
   output logic                 clk_o
);



  if (NUM_INPUTS<2)
    $error("Num inputs must be parametrized to a value >= 2.");

  // For each input, we generate an enable signal that enables the clock
  // propagation through an N-input clock OR gate. The crucial and most critical
  // part is to make sure that these clock enable signal transitions are
  // non-overlapping and have enough timing separation to prevent any glitches
  // on the clock output during the transition. We ensure this as follows:
  //
  // 1. Decode the sel_i input to a onehot signal.
  // 2. For each clock input, take the correspondi onehot signal. For each clock
  // input we also have a correspdonding output clock enable signal that
  // controls the corresponding clock's clk gate. We thus and-gate the one-hot
  // signal of the current clock with the inverse of every other clocks enable
  // signal. In other words, we only allow the propagation of the onehot enable
  // signal if the clock is currently disabled.
  // 3. Filter any glitches on this and-gated signal by passing it through a
  // flip-flop clocked by the current clock and and-gating both the output and
  // the input. I.e. the output is only becomes active if the signal stays
  // stable HIGH for at least one clock period.
  // 4. Synchronize this glitch-filtered signal into the current clock domain
  // with an M-stage synchronizer.
  // 5. Use this synchronized signal as the enable signal for a glitch-free
  // clock gate.
  // 7. Feed the output of the clock gate to an N-input clock-AND gate.
  // 8. Latch the gate enable signal with an active low latch before using the
  // signal as a gating signal for the other clock input's onehot signal.

  // Internal signals
  logic [NUM_INPUTS-1:0]        s_sel_onehot;
  (*dont_touch*)
  (*async_reg*)
  logic [NUM_INPUTS-1:0][1:0]   glitch_filter_d, glitch_filter_q;
  logic [NUM_INPUTS-1:0]        s_glitch_filter_output;
  logic [NUM_INPUTS-1:0]        s_gate_enable;
  logic [NUM_INPUTS-1:0]        clock_has_been_disabled_q;
  logic [NUM_INPUTS-1:0]        s_gated_clock;
  logic                         s_output_clock;


  // Onehot decoder
  always_comb begin
    s_sel_onehot = '0;
    s_sel_onehot[async_sel_i] = 1'b1;
  end

  // Input stages
  for (genvar i = 0; i < NUM_INPUTS; i++) begin : gen_input_stages
    // Gate onehot signal with other clocks' output gate enable
    always_comb begin
      glitch_filter_d[i][0] = 1'b1;
      for (int j = 0; j < NUM_INPUTS; j++) begin
        if (i==j) begin
          glitch_filter_d[i][0] &= s_sel_onehot[j];
        end else begin
          glitch_filter_d[i][0] &= clock_has_been_disabled_q[j];
        end
      end
    end
    assign glitch_filter_d[i][1] = glitch_filter_q[i][0];

    // Filter HIGH-pulse glitches
    always_ff @(posedge clks_i[i], negedge async_rstn_i) begin
      if (!async_rstn_i) begin
        glitch_filter_q[i] <= '0;
      end else begin
        glitch_filter_q[i] <= glitch_filter_d[i];
      end
    end
    assign s_glitch_filter_output[i] = glitch_filter_q[i][1] &
                                       glitch_filter_q[i][0] &
                                       glitch_filter_d[i][0];

    // Synchronize to current clock
    sync #(.STAGES(NUM_SYNC_STAGES)) i_sync_en(
      .clk_i    ( clks_i[i]                 ),
      .rst_ni   ( async_rstn_i              ),
      .serial_i ( s_glitch_filter_output[i] ),
      .serial_o ( s_gate_enable[i]          )
    );

    // Gate the input clock with the synced enable signal
    tc_clk_gating #(
      .IS_FUNCTIONAL(1'b1)
    ) i_clk_gate (
      .clk_i     ( clks_i[i]        ),
      .en_i      ( s_gate_enable[i] ),
      .test_en_i ( 1'b0             ),
      .clk_o     ( s_gated_clock[i] )
    );

    // Latch the enable signal with the next rising edge of the input clock and
    // feed the output back to the other stage's input. If we were to directly
    // use the clock gate enable signal to determine wether it is save to enable
    // another clock (i.e. the signal becomes low) we would risk enabling the
    // other clock to early. This is because the glitch free clock gate will
    // only really disable the clock with the next falling edge. By delaying the
    // enable signal one more cycle, we ensure that the clock stays low for at
    // least one clock period of the original clock input before any other clock
    // even has the chance to become active.

    always_ff @(posedge clks_i[i], negedge async_rstn_i) begin
      if (!async_rstn_i) begin
        clock_has_been_disabled_q[i] <= 1'b0;
      end else begin
        clock_has_been_disabled_q[i] <= ~s_gate_enable[i];
      end
    end
  end

  // Output OR-gate. At this stage, we should be already sure that the clocks
  // are enabled/disabled at the proper time to prevent any glitches from
  // escaping.

  clk_or_tree #(NUM_INPUTS) i_clk_or_tree (
    .clks_i(s_gated_clock),
    .clk_o(s_output_clock)
  );

  // Mux between the regular muxed clock and the test_clk_i used for DFT.
  tc_clk_mux2 i_test_clk_mux(
    .clk0_i(s_output_clock),
    .clk1_i(test_clk_i),
    .clk_sel_i(test_en_i),
    .clk_o
  );

endmodule

// Helper Module to generate an N-input clock OR-gate from a tree of tc_clk_or2 cells.
module clk_or_tree #(
  parameter int unsigned NUM_INPUTS
) (
  input logic [NUM_INPUTS-1:0] clks_i,
  output logic clk_o
);

  if (NUM_INPUTS < 1) begin : gen_error
    $error("Cannot parametrize clk_or with less then 1 input but was %0d", NUM_INPUTS);
  end else if (NUM_INPUTS == 1) begin : gen_leaf
    assign clk_o          = clks_i[0];
  end else if (NUM_INPUTS == 2) begin : gen_leaf
    tc_clk_or2 i_clk_or2 (
      .clk0_i(clks_i[0]),
      .clk1_i(clks_i[1]),
      .clk_o
    );
  end else begin  : gen_recursive
    logic branch_a, branch_b;
    clk_or_tree #(NUM_INPUTS/2) i_or_branch_a (
      .clks_i(clks_i[0+:NUM_INPUTS/2]),
      .clk_o(branch_a)
    );

    clk_or_tree #(NUM_INPUTS/2 + NUM_INPUTS%2) i_or_branch_b (
      .clks_i(clks_i[NUM_INPUTS-1:NUM_INPUTS/2]),
      .clk_o(branch_b)
    );

    tc_clk_or2 i_clk_or2 (
      .clk0_i(branch_a),
      .clk1_i(branch_b),
      .clk_o
    );
  end

endmodule
