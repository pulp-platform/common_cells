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
  parameter int unsigned NumTests = 10000;
  parameter time TClkIn = 10ns;
  parameter int  DivWidth = 8;
  parameter int  MaxWaitCycles = 2**(DivWidth+1);

  localparam time t_delta = 50ps;
  localparam int unsigned RstClkCycles = 10;
  localparam time         TA = TClkIn*0.2;
  localparam time         TT = TClkIn*0.8;

  logic clk, rstn;
  logic test_mode_en;
  logic [DivWidth-1:0] div;
  logic        valid,ready;
  logic        clk_out;

  time         target_tclk_half;
  int unsigned target_div_value;
  time         last_rising_edge;
  time         last_falling_edge;

  int          error_count = 0;

  typedef logic [DivWidth-1:0] payload_t;

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

  clk_even_int_div #(
    .DIV_VALUE_WIDTH(DivWidth)
  ) i_dut(
    .clk_i          ( clk          ),
    .rst_ni         ( rstn         ),
    .test_mode_en_i ( test_mode_en ),
    .div_i          ( dut_in.data  ),
    .div_valid_i    ( dut_in.valid ),
    .div_ready_o    ( dut_in.ready ),
    .clk_o(clk_out)
  );

  initial begin : apply_stimuli
    test_mode_en = 1'b0;
    valid        = 1'b0;
    $info("Resetting clock divider...");
    @(posedge rstn);
    in_driver.reset_in();
    for (int i = 0; i < NumTests; i++) begin
      int wait_cycl;
      assert(std::randomize(target_div_value)) else
        $error("Randomization failure");
      $info("Dividing input clock by %0d", target_div_value);
      in_driver.send(target_div_value);
      wait_cycl = $urandom_range(0, MaxWaitCycles);
      repeat(wait_cycl) @(posedge clk);
    end
    $info("Test finished");
  end

  assign target_tclk_half = TClkIn/target_div_value/2;

  initial begin : check_clock
    last_rising_edge = $realtime();
    last_falling_edge = $realtime();
    @(posedge rstn);
    forever begin
      automatic bit clock_transitioning = 0;
      @(posedge clk);
      assert($realtime()-last_falling_edge > target_tclk_half - t_delta) else begin
        $error("Detected rising edge glitch. Previous falling edge was %0t ago.", $realtime()-last_falling_edge);
        error_count++;
      end
      if (!clock_transitioning) begin
        assert($realtime()-last_falling_edge < target_tclk_half + t_delta) else begin
          $error("Detected wrong duty cycle. Target t_low period should be %0t but was %0t", target_tclk_half, $realtime()-last_falling_edge);
          error_count++;
        end
      end
      last_rising_edge = $realtime();
      @(negedge clk);
      if (dut_in.valid && dut_in.ready) begin
        clock_transitioning = 1'b1;
      end else begin
        assert($realtime()-last_rising_edge > target_tclk_half - t_delta) else begin
          $error("Detected wrong duty cycle. Last high period was to short (%0t instead of %0t).", $realtime()-last_rising_edge, target_tclk_half);
          error_count++;
        end
      end
      assert($realtime()-last_rising_edge < target_tclk_half + t_delta) else begin
        $error("Detected wrong duty cycle. Lat high period was to long (%0t instead of %0t).", $realtime()-last_rising_edge, target_tclk_half);
        error_count++;
      end
    end
  end



endmodule
