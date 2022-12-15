//-----------------------------------------------------------------------------
// Title         : TB to test the glitch free clock multiplexer
//-----------------------------------------------------------------------------
// File          : clk_mux_glitch_free_tb.sv
// Author        : Manuel Eggimann  <meggimann@iis.ee.ethz.ch>
// Created       : 11.12.2022
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

`define abs(x) (((x) < 0 )? -(x) : (x))
`define min(a,b) (((a) < (b))? (a) : (b))

module clk_mux_glitch_free_tb;
  timeunit 1ns;
  timeprecision 1ps;

  parameter int unsigned NUM_INPUTS = 10;
  localparam int unsigned SEL_WIDTH = $clog2(NUM_INPUTS);
  parameter realtime     MIN_PERIOD = 1ns;
  parameter realtime     MAX_PERIOD = 3ns;
  parameter realtime     TIME_RESOLUTION = 0.1ns;
  parameter int          TEST_LENGTH = 1000;

  logic [SEL_WIDTH-1:0]  s_sel    = '0;
  logic [NUM_INPUTS-1:0] s_clocks = '0;
  logic                  s_rstn;
  logic                  s_clock_output;
  realtime target_periods [NUM_INPUTS-1:0];
  int      num_errors = 0;

  task automatic delay_random(input realtime min_delay, input realtime max_delay);
    int delay_int = $urandom_range($rtoi(min_delay/TIME_RESOLUTION), $rtoi(max_delay/TIME_RESOLUTION));
    repeat(delay_int) #TIME_RESOLUTION;
  endtask

  // Generate input clocks with random period and random phase shift
  for (genvar i = 0; i < NUM_INPUTS; i++) begin : gen_clocks
    initial begin : clock_gen
      automatic int period_int;
      period_int = $urandom_range($rtoi(MIN_PERIOD/TIME_RESOLUTION), $rtoi(MAX_PERIOD/TIME_RESOLUTION));
      target_periods[i] = period_int * TIME_RESOLUTION;
      delay_random(0, MAX_PERIOD);
      forever begin
        s_clocks[i] = 1'b1;
        repeat(period_int/2) #(TIME_RESOLUTION);
        s_clocks[i] = 1'b0;
        repeat(period_int/2) #(TIME_RESOLUTION);
        end
    end
  end // block: gen_clocks

  // Randomly switch between clocks
  initial begin : stimulate_sel_input
    $info("Starting Test");
    $info("Asserting hard reset");
    s_rstn = 1'b0;
    s_sel = $urandom_range(0, NUM_INPUTS-1);
    delay_random(0, MAX_PERIOD);
    $info("Deasserting hard reset.");
    s_rstn = 1'b1;
    $info("Switching between clock inputs %0d times", TEST_LENGTH);
    for (int i = 0; i < TEST_LENGTH; i++) begin
      delay_random(MAX_PERIOD*10, MAX_PERIOD*30);
      s_sel = $urandom_range(0, NUM_INPUTS-1);
    end
    repeat(10) @(posedge s_clock_output);
    $info("Test finished with %0d errors.", num_errors);
    $stop();
  end

  // Check clock edges
  initial begin : check_clock
    automatic realtime last_high_pulse_duration = 0ns;
    automatic realtime last_low_pulse_duration  = 0ns;
    automatic realtime pulse_duraton            = 0ns;
    automatic realtime last_edge                = 0ns;
    $timeformat(-9, 3, "ns", 0);
    // The rules we check are as follows:
    // Every high pulse must have a duration of at least
    // min(previous period, next period)/2 
    // Every low period must have a duration of at leat <newly
    // selected_clk_period/2>.
    @(posedge s_rstn);
    forever begin
      @(posedge s_clock_output);
      pulse_duraton = $realtime - last_edge;
      if (`abs(last_low_pulse_duration - pulse_duraton) > TIME_RESOLUTION) begin
        assert(pulse_duraton + TIME_RESOLUTION >= target_periods[s_sel]/2) else
          $error("Error #%0d: Clock low pulse duration was %t but should be larger than %t", num_errors++, pulse_duraton, target_periods[s_sel]/2);        
      end
      last_edge = $realtime;
      last_low_pulse_duration = pulse_duraton;
      @(negedge s_clock_output);
      pulse_duraton = $realtime - last_edge;
      if (`abs(last_high_pulse_duration - pulse_duraton) > TIME_RESOLUTION) begin
        assert( `abs(pulse_duraton - target_periods[s_sel]/2) <= TIME_RESOLUTION) else
          $error("Error #%0d: Clock high pulse duration was %t but should be equal to %t", num_errors++, pulse_duraton, target_periods[s_sel]/2);
        end
      last_edge = $realtime;
      last_high_pulse_duration = pulse_duraton;
    end
  end // block: check_clock

  clk_mux_glitch_free #(
    .NUM_INPUTS(NUM_INPUTS)
  ) i_dut (
    .clks_i       ( s_clocks       ),
    .test_clk_i   ( 1'b0           ),
    .test_en_i    ( 1'b0           ),
    .async_rstn_i ( s_rstn         ),
    .async_sel_i  ( s_sel          ),
    .clk_o        ( s_clock_output )
  );
  
endmodule
