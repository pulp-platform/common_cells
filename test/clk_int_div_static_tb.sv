//-----------------------------------------------------------------------------
// Copyright (C) 2023 ETH Zurich, University of Bologna
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

module clk_int_div_static_tb;
  parameter   int unsigned NumTestCycles = 10000;
  parameter realtime       TClkIn = 10ns;
  localparam int unsigned  RstClkCycles = 10;

  localparam int unsigned  MaxClkDiv = 100;

  realtime          t_delta             = 100ps;

  logic                    clk, rstn;
  logic                    test_mode_en;
  logic                    enable;
  logic                    clk_out [MaxClkDiv];


  // system clock and reset
  clk_rst_gen #(
    .ClkPeriod    ( TClkIn ),
    .RstClkCycles ( RstClkCycles   )
  ) i_clk_rst_gen_reg (
    .clk_o  ( clk  ),
    .rst_no ( rstn )
  );

  property T_clk(real clk_period);
    realtime               current_time;
    realtime               actual_period;
    disable iff (!rstn || !enable)
      (('1, current_time = $realtime)) |=>
                           ('1, actual_period = $realtime - current_time) |->
                           (($realtime - current_time >= clk_period - t_delta) && ($realtime - current_time < clk_period + t_delta));
  endproperty


  for (genvar i = 1; i < MaxClkDiv; i++) begin :gen_clk_divs
    clk_int_div_static #(
      .DIV_VALUE(i)
    ) i_dut(
      .clk_i          ( clk          ),
      .rst_ni         ( rstn         ),
      .en_i           ( enable       ),
      .test_mode_en_i ( test_mode_en ),
      .clk_o          ( clk_out[i]   )
    );

    assert_period_period: assert property (@(posedge clk_out[i]) T_clk(TClkIn*i)) else
      $error("Output period of div-2 clock is incorrect. Should be in range %d to %d.", TClkIn*i-t_delta, TClkIn*i+t_delta);

  end

  initial begin : apply_stimuli
    test_mode_en = 1'b0;
    enable       = 1'b1;
    $info("Resetting clock dividers...");
    @(posedge rstn);

    // Randomly enable and disable the output clock
    repeat(NumTestCycles) begin
      @(posedge clk);
      if ($urandom_range(0, 1000)<5) begin
        enable = 1'b0;
        repeat($urandom_range(1, 100)) @(posedge clk);
        enable = 1'b1;
      end
    end
    $info("Test finished");
    $stop();
  end

endmodule
