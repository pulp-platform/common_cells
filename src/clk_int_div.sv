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
// other clk_div change request is accepted. clk_o remains gated for at most
// 3x<new clk period> clk_i cycles. If the new div_i value equals the currently
// configured value, the clock is not gated and the handshake is immediately
// granted. It is thus safe to statically tie the valid signal to logic high if
// we can guarantee, that the div_i value remains stable long enough (upper
// limit 2 output clock cycles).
//
// The `en_i` signal can be used to enable or disable the output clock in a safe
// manner.
//
// If a div value of 0 or 1 is requested, the input clock is feed through to the
// output clock. However, the same gating rules apply (again to prevent
// glitches).
//
// If test_mode_en_i is asserted, the output clock gate is bypassed entirely and
// clk_o will always be directly driven by clk_i. Use this mode for DFT of the
// downstream logic.
//
// Parameters: DIV_VALUE_WIDTH: The number of bits to use for the internal
// counter. Defines the maximum division factor.
//
// DEFAULT_DIV_VALUE: The default division factor to use after reset. Use this
// parameter and tie div_valid_i to zero if you don't need at runtime
// configurability. An elaboration time error will be issued if the supplied
// default div value is not repressentable with DIV_VALUE_WIDTH bits.
//
// ENABLE_CLOCK_IN_RESET: If 1'b1, clk_o will not be gated during reset and will
// immediately start clocking with the configured DEFAULT_DIV_VALUE. (Disabled
// by default).
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

module clk_int_div #(
  /// The with
  parameter int unsigned DIV_VALUE_WIDTH = 4,
  /// The default divider value which is used right after reset
  parameter int unsigned DEFAULT_DIV_VALUE = 0,
  /// If 1'b1, the output clock is enabled during async reset assertion
  parameter bit          ENABLE_CLOCK_IN_RESET = 1'b0
) (
  input logic                        clk_i,
  input logic                        rst_ni,
  /// Active-high output clock enable. Controls a glitch-free clock gate so the
  /// enable signal may be driven by combinational logic without introducing
  /// glitches.
  input logic                        en_i,
  /// If asserted (active-high) bypass the clock divider and drive clk_o
  /// directly with clk_i.
  input logic                        test_mode_en_i,
  /// Divider select value. The output clock has a frequency of f_clk_i/div_i.
  /// For div_i == 0 or  div_i == 1, the output clock has the same frequency as
  /// th input clock.
  input logic [DIV_VALUE_WIDTH-1:0]  div_i,
  /// Valid handshake signal. Must not combinationally depend on `div_ready_o`.
  /// Once asserted, the valid signal must not be deasserted until it is
  /// accepted with `div_ready_o`.
  input logic                        div_valid_i,
  output logic                       div_ready_o,
  /// Generated output clock. Given a glitch free input clock, the output clock
  /// is guaranteed to be glitch free with 50% duty cycle, regardless the timing
  /// of reconfiguration requests or en_i de/assetion. During the
  /// reconfiguration, the output clock is gated with its next falling edge and
  /// remains gated (idle-low) for at least one period of the new target output
  /// period to filter out any glitches during the config transition.
  output logic                       clk_o,
  /// Current value of the internal cycle counter. Might be usefull if you need
  /// to do some phase shifting relative to the generated clock.
  output logic [DIV_VALUE_WIDTH-1:0] cycl_count_o
);

  if ($clog2(DEFAULT_DIV_VALUE+1) > DIV_VALUE_WIDTH) begin : gen_elab_error
    $error("Default divider value %0d is not representable with the configured",
            "div value width of %0d bits.",
           DEFAULT_DIV_VALUE, DIV_VALUE_WIDTH);
  end

  // We have to preset the div_q register with a value larger than one to avoid
  // an infinite loop in the WAIT_END_PERIOD state. If the default state of the
  // clock divider should be bypass, we thus always preset the div_q with 1
  // rather than 1 or zero.
  localparam int unsigned DivResetValue = (DEFAULT_DIV_VALUE != 0)? DEFAULT_DIV_VALUE: 1;

  logic [DIV_VALUE_WIDTH-1:0] div_i_normalized;
  logic [DIV_VALUE_WIDTH-1:0] div_d, div_q;
  logic                       toggle_ffs_en;
  logic                       t_ff1_d, t_ff1_q;
  logic                       t_ff1_en;

  logic                       t_ff2_d, t_ff2_q;
  logic                       t_ff2_en;

  logic [DIV_VALUE_WIDTH-1:0]   cycle_cntr_d, cycle_cntr_q;
  logic                         cycle_counter_en;
  logic                         clk_div_bypass_en_d, clk_div_bypass_en_q;
  logic                         odd_clk;
  logic                         even_clk;
  logic                         generated_clock;
  logic                         ungated_output_clock;

  logic                         use_odd_division_d, use_odd_division_q;
  logic                         gate_en_d, gate_en_q;
  logic                         gate_is_open_q;
  logic                         clear_cycle_counter;
  logic                         clear_toggle_flops;

  typedef enum logic[1:0] {IDLE, LOAD_DIV, WAIT_END_PERIOD} clk_gate_state_e;
  clk_gate_state_e clk_gate_state_d, clk_gate_state_q;

  // Normalize the div_i value. div_i == 0 and div_i == 1 have the same meaning
  // but actually loading 0 causes issues in the FSM. We thus always load 1 for
  // both cases
  assign div_i_normalized = (div_i != 0)? div_i : 1;


  //-------------------- Divider Load FSM --------------------
  always_comb begin
    div_d               = div_q;
    div_ready_o         = 1'b0;
    clk_div_bypass_en_d = clk_div_bypass_en_q;
    use_odd_division_d  = use_odd_division_q;
    clk_gate_state_d    = clk_gate_state_q;
    cycle_counter_en    = 1'b1;
    clear_cycle_counter = 1'b0;
    clear_toggle_flops  = 1'b0;
    toggle_ffs_en       = 1'b1;

    gate_en_d           = 1'b0;
    clk_gate_state_d    = clk_gate_state_q;
    case (clk_gate_state_q)
      IDLE: begin
        gate_en_d     = 1'b1;
        toggle_ffs_en = 1'b1;
        if (div_valid_i) begin
          if (div_i_normalized == div_q) begin
            div_ready_o      = 1'b1;
          end else begin
            clk_gate_state_d = LOAD_DIV;
            gate_en_d        = 1'b0;
          end
        // If we disabled the clock output, stop the cycle counter and the
        // toggle flip-flops at the start of the next period to safe energy.
        end else if (!en_i && gate_is_open_q == 1'b0) begin
            cycle_counter_en                 = 1'b0;
            toggle_ffs_en                    = 1'b0;
        end
      end

      LOAD_DIV: begin
        gate_en_d                 = 1'b0;
        toggle_ffs_en             = 1'b1;
        // Wait until the ouptut clock is currently deasserted. This ensures
        // that the clock gate disable (gate_en) was latched and changing the
        // div_q and the cycle_counter_q value cannot affect the output clock
        // any longer.
        if ((gate_is_open_q == 1'b0) || clk_div_bypass_en_q) begin
          // Now clear the cycle counter and the toggle flip flops to have a
          // deterministic output phase (rising edge of output clock always
          // coincides with first rising edge of input clock when cycl_count_o
          // == 0).
          toggle_ffs_en           = 1'b0;
          div_d                   = div_i_normalized;
          div_ready_o             = 1'b1;
          clear_cycle_counter     = 1'b1;
          clear_toggle_flops      = 1'b1;
          use_odd_division_d      = div_i_normalized[0];
          clk_div_bypass_en_d     = div_i_normalized == 1;
          clk_gate_state_d        = WAIT_END_PERIOD;
        end
      end

      WAIT_END_PERIOD: begin
        gate_en_d     = 1'b0;
        // Keep the toggle flip-flops disabled until we reach idle state.
        // Otherwise, the start state of the t-ffs depends on the number of wait
        // cycles which would yield different output clock phase depending on
        // the number of wait cycles.
        toggle_ffs_en = 1'b0;
        if (cycle_cntr_q == div_q - 1) begin
          clk_gate_state_d = IDLE;
        end
      end

      default: begin
        clk_gate_state_d = IDLE;
      end
    endcase
  end

  localparam logic UseOddDivisionResetValue = DEFAULT_DIV_VALUE[0];
  localparam logic ClkDivBypassEnResetValue = (DEFAULT_DIV_VALUE < 2)? 1'b1: 1'b0;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      use_odd_division_q  <= UseOddDivisionResetValue;
      clk_div_bypass_en_q <= ClkDivBypassEnResetValue;
      div_q               <= DivResetValue;
      clk_gate_state_q    <= IDLE;
      gate_en_q           <= ENABLE_CLOCK_IN_RESET;
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
    cycle_cntr_d = cycle_cntr_q;
    // Reset the counter if we load a new divider value.
    if (clear_cycle_counter) begin
      cycle_cntr_d = '0;
    end else begin
      if (cycle_counter_en) begin
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
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_cntr_q <= '0;
    end else begin
      cycle_cntr_q <= cycle_cntr_d;
    end
  end

  assign cycl_count_o = cycle_cntr_q;

  //----------------------- T-Flip-Flops -----------------------

  // These T-Flip-Flop intentionally use blocking assignments! If we were to use
  // non-blocking assignment like we normally do for flip-flops, we would create
  // a race condition when sampling data from the fast clock domain into
  // flip-flops clocked by t_ff1_q and t_ff2_q. To avoid this, we use blocking assignments
  // which is the recomended method acording to:
  // S. Sutherland and D. Mills,
  // Verilog and System Verilog gotchas: 101 common coding errors and how to
  // avoid them. New York: Springer, 2007. page 64.

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
  always_ff @(negedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      t_ff2_q = '0; // Intentional blocking assignment! Do not replace!
    end else begin
      if (t_ff2_en) begin
        t_ff2_q = t_ff2_d; // Intentional blocking assignment! Do not replace!
      end
    end
  end

  always_comb begin
    if (clear_toggle_flops) begin
      t_ff1_d = '0;
      t_ff2_d = '0;
    end else begin
      t_ff1_d = t_ff1_en? !t_ff1_q: t_ff1_q;
      t_ff2_d = t_ff2_en? !t_ff2_q: t_ff2_q;
    end
  end


  //----- FSM to control T-FF enable and clk_div_bypass_en -----

  always_comb begin
    t_ff1_en = 1'b0;
    t_ff2_en = 1'b0;
    if (!clk_div_bypass_en_q && toggle_ffs_en) begin
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

  // The gate_is_open_q signal is used by the FSM to determine whether the
  // gate_en signal has been latched by the clock gate cell, i.e. if this signal
  // is 1'b0, it means not only that the clock gate should be disabled but also that
  // clk_o is currently LOW and thus the enable signal has been latched and the
  // output clock will remain LOW until we enable the clock again.
  // The FSM needs to know this to not disable the T-FFs and the cycle counter
  // to early. Otherwise the clock might get stuck active high or we deassert a
  // clock to early
  always_ff @(posedge ungated_output_clock, negedge rst_ni) begin
    if (!rst_ni) begin
      gate_is_open_q <= 1'b0;
    end else begin
      gate_is_open_q <= gate_en_q & en_i;
    end
  end

  tc_clk_gating #(
    .IS_FUNCTIONAL(1) // The gate is required to prevent glitches during
                      // transitioning. Target specific implementations must not
                      // remove it to save ICGs (e.g. in FPGAs).
  ) i_clk_gate (
    .clk_i     ( ungated_output_clock ),
    .en_i      ( gate_en_q & en_i     ),
    .test_en_i ( test_mode_en_i       ),
    .clk_o
  );


endmodule
