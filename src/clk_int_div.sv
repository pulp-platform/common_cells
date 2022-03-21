//-----------------------------------------------------------------------------
// Title : Configurable Integer Clock Divider
// -----------------------------------------------------------------------------
// File : clk_int_div.sv Author : Manuel Eggimann <meggimann@iis.ee.ethz.ch>
// Created : 17.03.2022
// -----------------------------------------------------------------------------
// Description :
//
// This module implements an at runtime configurable integer clock divider that
// always generates clean 50% duty cycle output clock. Clock divider setting
// changes are handshaked and during the transitioning phase between clk_div
// value changes, the output clock is gated to prevent clock glitches and no
// other clk_div change request is accepted. Clk_o remains gated for at least
// 2x<new clk period> clk_i cycles.
//
// If a div value of 0 or 1 is requested, the input clock is feed through to the
// output clock. However, the same gating rules apply (again to prevent
// glitches).
//
// If test_mode_en_i is asserted, the output clock gate is bypassed entirely and
// clk_o will always be directly driven by clk_i. Use this mode for DFT of the
// downstream logic.
//
//-----------------------------------------------------------------------------
// Copyright (C) 2022 ETH Zurich, University of Bologna Copyright and related
// rights are licensed under the Solderpad Hardware License, Version 0.51 (the
// "License"); you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law or
// agreed to in writing, software, hardware and materials distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, either express or implied. See the License for the specific
// language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
// -----------------------------------------------------------------------------

module clk_even_int_div #(
  parameter int unsigned DIV_VALUE_WIDTH = 4,
  parameter int unsigned DEFAULT_DIV_VALUE = 0
) (
  input logic                       clk_i,
  input logic                       rst_ni,
  input logic                       en_i,
  /// If asserted (active-high) bypass the clock divider and drive clk_o directly with clk_i.
  input logic                       test_mode_en_i,
  /// Divider select value. The output clock has a frequency of f_clk_i/div_i.
  /// For div_i == 0 or  div_i == 1, the output clock has the same frequency as
  /// th input clock.
  input logic [DIV_VALUE_WIDTH-1:0] div_i, // divider selection, the actual division value is div_i*2
  input logic                       div_valid_i,
  output logic                      div_ready_o,
  output logic                      clk_o
);

  logic [DIV_VALUE_WIDTH-1:0]	div_d, div_q;
  logic                       t_ff1_d, t_ff1_q;
  logic                       t_ff1_en;

  logic                       t_ff2_d, t_ff2_q;
  logic                       t_ff2_en;

  logic [DIV_VALUE_WIDTH:0]   	cycle_cntr_d, cycle_cntr_q; // +1 bit because div_i has to be multiplied by 2
  logic                         clk_div_bypass_en_d, clk_div_bypass_en_q;
  logic                         odd_clk;
  logic                         even_clk;
  logic                         generated_clock;
  logic                         ungated_output_clock;
  logic                         use_odd_division_d, use_odd_division_q;
  logic                         gate_en_d, gate_en_q;

  typedef enum logic[1:0] {IDLE, LOAD_DIV, WAIT_START_PERIOD, WAIT_END_PERIOD} clk_gate_state_e;
  clk_gate_state_e clk_gate_state_d, clk_gate_state_q;

  //-------------------- Divider Load FSM --------------------
  always_comb begin
    div_d               = div_q;
    div_ready_o         = 1'b0;
    clk_div_bypass_en_d = clk_div_bypass_en_q;
    use_odd_division_d  = use_odd_division_q;
    clk_gate_state_d    = clk_gate_state_q;

    gate_en_d           = 1'b0;
    clk_gate_state_d    = clk_gate_state_q;
    case (clk_gate_state_q)
      IDLE: begin
        gate_en_d = 1'b1;
        if (!en_i) begin
          gate_en_d = 1'b0;
        end else if (div_valid_i) begin
          clk_gate_state_d = LOAD_DIV;
          gate_en_d = 1'b0;
        end
      end

      LOAD_DIV: begin
        gate_en_d = 1'b0;
        // Wait until the ouptut clock is currently deasserted. This ensures
        // that the clock gate disable (gate_en) was latched and changing the
        // div_q and the cycle_counter_q value cannot affect the output clock
        // any longer.
        if ((ungated_output_clock == 1'b0) || clk_div_bypass_en_q) begin
          div_d               = div_i;
          div_ready_o         = 1'b1;
          use_odd_division_d  = div_i[0];
          clk_div_bypass_en_d = (div_i == 0) || (div_i == 1);
          clk_gate_state_d    = WAIT_START_PERIOD;
        end
      end

      WAIT_START_PERIOD: begin
        gate_en_d        = 1'b0;
        if (cycle_cntr_q == '0) begin
          clk_gate_state_d = WAIT_END_PERIOD;
        end
      end

      WAIT_END_PERIOD: begin
        gate_en_d        = 1'b0;
        if (cycle_cntr_q == div_q -1 || clk_div_bypass_en_q) begin
          clk_gate_state_d = IDLE;
        end
      end
    endcase

    if (div_valid_i) begin
      if (clk_gate_state_q == LOAD_DIV) begin

      end else begin
        div_ready_o = 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      use_odd_division_q  <= 1'b0;
      clk_div_bypass_en_q <= 1'b1;
      div_q               <= DEFAULT_DIV_VALUE;
      clk_gate_state_q    <= IDLE;
      gate_en_q           <= 1'b0;
    end else begin
      use_odd_division_q  <= use_odd_division_d;
      clk_div_bypass_en_q <= clk_div_bypass_en_d;
      div_q               <= div_d;
      clk_gate_state_q    <= clk_gate_state_d;
      gate_en_q           <= gate_en_d;
    end
  end

  //---------------------- Cycle Counter ----------------------

  // Cycle Counter
  always_comb begin
    // Reset the counter if we load a new divider value.
    if (div_valid_i && div_ready_o) begin
      cycle_cntr_d = '0;
    end else begin
      // During normal operation, reset the counter whenver it reaches
      // <target_count>-1. In bypass mode (div == 0 or div == 1) disable the
      // counter to save power.
      if (clk_div_bypass_en_q || (cycle_cntr_q == div_q-1)) begin
        cycle_cntr_d = '0;
      end else begin
        cycle_cntr_d = cycle_cntr_q + 1;
      end
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_cntr_q <= '0;
    end else begin
      cycle_cntr_q <= cycle_cntr_d;
    end
  end

  //----------------------- T-Flip-Flops -----------------------

  // These T-Flip-Flop intentionally use blocking assignments! If we were to use
  // non-blocking assignment like we normally do for flip-flops, we would create
  // a race condition when sampling data from the fast clock domain into
  // flip-flops clocked by t_ff1_q and t_ff2_q. To avoid this, we use blocking assignments
  // which is the reccomended method acording to:
  // S. Sutherland and D. Mills,
  // Verilog and System Verilog gotchas: 101 common coding errors and how to
  // avoid them. New York: Springer, 2007. page 64.
  assign t_ff1_d = !t_ff1_q;
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      t_ff1_q = '0; // Intentional blocking assignment! Do not replace!
    end else begin
      if (t_ff1_en) begin
        t_ff1_q = t_ff1_d; // Intentional blocking assignment! Do not replace!
      end
    end
  end

  // The second flip-flop is required for odd integer division and needs to
  // negative edge tirggered.
  assign t_ff2_d = !t_ff2_q;
  always_ff @(negedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      t_ff2_q = '0; // Intentional blocking assignment! Do not replace!
    end else begin
      if (t_ff2_en) begin
        t_ff2_q = t_ff2_d; // Intentional blocking assignment! Do not replace!
      end
    end
  end

  //----- FSM to control T-FF enable and clk_div_bypass_en -----

  always_comb begin
    t_ff1_en = 1'b0;
    t_ff2_en = 1'b0;
    if (!clk_div_bypass_en_q) begin
      if (use_odd_division_q) begin
        t_ff1_en = (cycle_cntr_q == 0)? 1'b1: 1'b0;
        t_ff2_en = (cycle_cntr_q == (div_q+1)/2)? 1'b1: 1'b0;
      end else begin
        t_ff1_en = (cycle_cntr_q == 0 || cycle_cntr_q == div_q/2)? 1'b1: 1'b0;
      end
    end
  end

  assign even_clk = t_ff1_q;

  //----------- Clock XOR for the odd division logic -----------
  tc_clk_xor2 i_odd_clk_xor (
    .clk0_i ( t_ff1_q ),
    .clk1_i ( t_ff2_q ),
    .clk_o  ( odd_clk )
  );

  //---- Clock MUX to select between odd and even div logic ----
  tc_clk_mux2 i_clk_mux (
    .clk0_i    ( even_clk           ),
    .clk1_i    ( odd_clk            ),
    .clk_sel_i ( use_odd_division_q ),
    .clk_o     ( generated_clock    )
  );

  //-------------------- clock mux to bypass clock if divide-by-1  --------------------
  tc_clk_mux2 i_clk_bypass_mux (
    .clk0_i    ( generated_clock                       ),
    .clk1_i    ( clk_i                                 ),
    .clk_sel_i ( clk_div_bypass_en_q || test_mode_en_i ),
    .clk_o     ( ungated_output_clock                  )
  );

  //--------------------- Clock gate logic ---------------------
  // During the transitioning phase, we gate the clock to prevent clock glitches

  tc_clk_gating #(
    .IS_FUNCTIONAL(1) // The gate is required to prevent glitches during
                      // transitioning. Target specific implementations must not
                      // remove it to save ICGs (e.g. in FPGAs).
  ) i_clk_gate (
    .clk_i     ( ungated_output_clock        ),
    .en_i      ( gate_en_q || test_mode_en_i ),
    .test_en_i ( test_mode_en_i              ),
    .clk_o
  );


endmodule
