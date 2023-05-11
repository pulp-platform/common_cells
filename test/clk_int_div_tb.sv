//-----------------------------------------------------------------------------
// Title         : TB to test the integer clock divider IP
//-----------------------------------------------------------------------------
// File          : clk_int_div_tb.sv
// Author        : Manuel Eggimann  <meggimann@iis.ee.ethz.ch>
// Created       : 17.03.2022
//-----------------------------------------------------------------------------
// Copyright (C) 2022 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//-----------------------------------------------------------------------------

module clk_int_div_tb;
  import stream_test::*;
  parameter int unsigned NumTests = 10000;
  parameter time TClkIn = 10ns;
  parameter int  DivWidth = 3;
  parameter int  MaxWaitCycles = 20;

  localparam time t_delta = 1ns;
  localparam int unsigned RstClkCycles = 10;
  localparam time         TA = TClkIn*0.2;
  localparam time         TT = TClkIn*0.8;
  localparam clock_disable_probability = 5; // 5% of the tested div settings the
                                            // clock is randomly disabled for a
                                            // couple of cycles

  logic clk, rstn;
  logic test_mode_en;
  logic enable;
  logic        clk_out;
  semaphore semphr_is_transitioning;
  bit is_transitioning = 1'b0;

  int                  wait_cycl;
  time                 target_tclk_half_max;
  time                 target_tclk_half_min;
  logic [DivWidth-1:0] current_div_value;
  logic [DivWidth-1:0] next_div_value;
  time                 last_rising_edge;
  time                 last_falling_edge;

  int          error_count = 0;

  typedef logic [DivWidth-1:0] payload_t;
  let max(a,b) = (a > b) ? a : b;
  let min(a,b) = (a < b) ? a : b;

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (TA),
    .TT (TT)
  ) stream_driver_t;

  STREAM_DV #(
    .payload_t (payload_t)
  ) dut_in (
    .clk_i (clk)
  );

  stream_driver_t in_driver = new(dut_in);

  // system clock and reset
  clk_rst_gen #(
    .ClkPeriod    ( TClkIn ),
    .RstClkCycles ( RstClkCycles   )
  ) i_clk_rst_gen_reg (
    .clk_o  ( clk  ),
    .rst_no ( rstn )
  );

  clk_int_div #(
    .DIV_VALUE_WIDTH(DivWidth)
  ) i_dut(
    .clk_i          ( clk          ),
    .rst_ni         ( rstn         ),
    .en_i           ( enable       ),
    .test_mode_en_i ( test_mode_en ),
    .div_i          ( dut_in.data  ),
    .div_valid_i    ( dut_in.valid ),
    .div_ready_o    ( dut_in.ready ),
    .clk_o          ( clk_out      ),
    .cycl_count_o   (              )
  );

  initial begin : apply_stimuli
    semphr_is_transitioning = new();
    test_mode_en      = 1'b0;
    enable            = 1'b1;
    next_div_value    = 1;
    current_div_value = 1;
    $info("Resetting clock divider...");
    @(posedge rstn);
    in_driver.reset_in();


    // Verify test bypass mode
    test_mode_en = 1'b1;
    semphr_is_transitioning.put();
    repeat (100) @(clk);
    test_mode_en = 1'b0;

    $info("Testing programming divider while clock disabled...");
    enable = 1'b0;
    next_div_value = 3;
    semphr_is_transitioning.put(1);
    wait_cycl = $urandom_range(5*current_div_value, MaxWaitCycles*current_div_value);
    repeat(wait_cycl) @(posedge clk);
    in_driver.send(next_div_value);
    current_div_value = next_div_value;
    semphr_is_transitioning.put(1);
    @(posedge clk);
    enable = 1'b1;
    repeat(20) @(posedge clk);

    $info("Starting randomized reconfiguration while clock is enabled...");

    for (int i = 0; i < NumTests; i++) begin
      logic [DivWidth-1:0] div_value_temp;
      assert(std::randomize(div_value_temp)) else
        $error("Randomization failure");
      $info("Setting clock divider value to %0d", next_div_value);
      next_div_value = (div_value_temp == 0)? 1: div_value_temp;
      in_driver.send(div_value_temp);
      semphr_is_transitioning.put(1);
      current_div_value = next_div_value;
      wait_cycl = $urandom_range(0, MaxWaitCycles);
      repeat(wait_cycl) @(posedge clk_out);
      if ($urandom_range(0, 100) < clock_disable_probability) begin
        repeat(4) @(posedge clk_out);
        enable = 1'b0;
        semphr_is_transitioning.put(1);
        wait_cycl = $urandom_range(5*current_div_value, MaxWaitCycles*current_div_value);
        repeat(wait_cycl) @(posedge clk);
        enable = 1'b1;
        repeat(wait_cycl) @(posedge clk_out);
      end
    end
    $info("Test finished");
    $info("Total error count: %0d", error_count);
    $stop();
  end

  initial begin : check_clock
    last_rising_edge     = $realtime();
    last_falling_edge    = $realtime();
    target_tclk_half_max = TClkIn+t_delta;
    target_tclk_half_min = TClkIn-t_delta;
    @(posedge rstn);
    forever begin
      // Set target clock period boundaries. During the transition phase after
      // reprogramming we have relaxed boundaries since we might still get one
      // clock cycle with the old divider settings.
      @(posedge clk_out);
      // Ignore low period lenght during transition phase since the clock is
      // gated for ~ 1 output clock cycles
      is_transitioning =  semphr_is_transitioning.try_get(1);
      if (is_transitioning) begin
        target_tclk_half_max = TClkIn*max(current_div_value, next_div_value)/2+t_delta;
        target_tclk_half_min = TClkIn*min(current_div_value, next_div_value)/2-t_delta;
      end else begin
        target_tclk_half_max = TClkIn*current_div_value/2+t_delta;
        target_tclk_half_min = TClkIn*current_div_value/2-t_delta;
        assert($realtime()-last_falling_edge < target_tclk_half_max) else begin
          $error("Detected wrong duty cycle. Target t_low period should be lower than %0t ns but was %0t ns", target_tclk_half_max, $realtime()-last_falling_edge);
          error_count++;
        end
      end
      assert($realtime()-last_falling_edge > target_tclk_half_min) else begin
        $error("Detected clock glitch. Last low period was to short (%0t ns < %0t ns).", $realtime()-last_falling_edge, target_tclk_half_min);
        error_count++;
      end
      last_rising_edge = $realtime();
      @(negedge clk_out);
      assert($realtime()-last_rising_edge > target_tclk_half_min) else begin
        $error("Detected wrong duty cycle. Last high period was to short (%0t ns < %0t ns).", $realtime()-last_rising_edge, target_tclk_half_min);
        error_count++;
      end
      assert($realtime()-last_rising_edge < target_tclk_half_max) else begin
        $error("Detected wrong duty cycle. Last high period was to long (%0t ns >  %0t ns).", $realtime()-last_rising_edge, target_tclk_half_max);
        error_count++;
      end
      last_falling_edge = $realtime();
    end
  end



endmodule
