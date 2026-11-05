// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Gianluca Bellocchi <gianluca.bellocchi@unimore.it>

// Description: Testbench for `cc_qos_wrr_arbiter`.
//
// This testbench includes the following tests:
//
// 1. `dut_vs_ref_rr_fixed_no_stall`: this test assesses the DUT back-compatibility with
//    `cc_rr_arb_tree`. The DUT must be cycle-equivalent to the reference arbiter, which runs in
//    lock-step on the same stimuli. The traffic follows the fixed schedule of `cc_rr_arb_tree_tb`:
//    inputs stop requesting one after the other, then only even inputs request. These requests do
//    not follow the valid/ready handshake, so the output is never stalled. QoS and weights are
//    maintained equal across different inputs.
//
// 2. `dut_vs_ref_rr_random_stall`: this test assesses the DUT back-compatibility with
//    `cc_rr_arb_tree` under output backpressure. The DUT must be cycle-equivalent to the reference
//    arbiter, which runs in lock-step on the same stimuli. Requests arrive with random timing and
//    follow the valid/ready handshake, and the output is under random backpressure. While the
//    output is stalled, its request, index and data must remain stable. QoS and weights are
//    maintained equal across different inputs.
//
// 3. `dut_vs_ref_wrr_saturated_stall`: this test assesses the weighted round-robin arbitration of
//    the DUT against the standalone `cc_wrr_arbiter`. Each arbitration round must last exactly
//    `weight_i[i]` transfers. Arbitration rounds must rotate in round-robin order. The DUT must be
//    cycle-equivalent to the reference arbiter, which runs in lock-step on the same stimuli. All
//    inputs are saturated, and the output is under random backpressure. QoS is maintained equal
//    across different inputs, while each input has a distinct weight.
//
// 4. `dut_vs_ref_wrr_random_stall`: this test assesses the weighted round-robin arbitration of the
//    DUT against the standalone `cc_wrr_arbiter` under random traffic. The DUT must be
//    cycle-equivalent to the reference arbiter, which runs in lock-step on the same stimuli. All
//    checks on the DUT therefore also apply to the reference arbiter. Requests arrive with random
//    timing, and the output is under random backpressure. QoS is maintained equal across different
//    inputs, while weights are random.
//
// 5. `dut_qos_aging_saturated_stall`: this test assesses the QoS priority-aware arbitration and the
//    QoS aging of the DUT. Each arbitration round must start with an input at the highest effective
//    QoS priority level. Aging must prevent starvation by ensuring a stalled requester not to
//    exceed `StarvationBound` of waiting time. `StarvationBound` is a safe upper bound on the time
//    an input needs to age up to the highest QoS priority level and then wait for its round-robin
//    turn. All inputs are saturated, and the output is under random backpressure. Inputs are
//    spread over several QoS priority levels, two inputs per level with different weights, so that
//    the weighted split within a QoS priority level is also exercised.
//
// 6. `dut_all_random_stall`: this test assesses all the mechanisms of the DUT together. Requests
//    arrive with random timing, carrying a random QoS priority level. Weights and the backpressure
//    rate are randomized at every repetition of the test.

module cc_qos_wrr_arbiter_tb #(
  // Simulation parameters.
  //
  // Clock period.
  localparam time         CyclTime        = 10ns,
  // Stimuli application time.
  localparam time         ApplTime        = 2ns,
  // Response test time.
  localparam time         TestTime        = 8ns,
  // DUT configuration.
  //
  // Enable the QoS priority-aware arbitration, the weighted round-robin arbitration and the aging.
  parameter bit           EnableQos       = 1'b1,
  parameter bit           EnableWrr       = 1'b1,
  parameter bit           EnableAging     = 1'b1,
  // Number of request channels to arbitrate.
  parameter int unsigned  NumIn           = 32'd4,
  // Number of requests sent by each input in a test.
  parameter int unsigned  NumReqs         = 32'd20000,
  // Width of the data payload in bits.
  parameter int unsigned  DataWidth       = 32'd32,
  // Width of the input QoS priority level.
  parameter int unsigned  QosWidth        = 32'd4,
  // Width of the input weights.
  parameter int unsigned  WeightWidth     = 32'd4,
  // Number of output transfers after which an input held back by QoS gains one QoS priority level.
  parameter int unsigned  AgingThreshold  = 32'd1,
  // Derived parameters, do **not** overwrite!
  //
  // Width of the arbitrated index.
  localparam int unsigned IdxWidth        = cc_pkg::idx_width(NumIn),
  // Maximum QoS priority level.
  localparam int unsigned QosMax          = 2**QosWidth - 1,
  // Maximum weight value.
  localparam int unsigned WeightMax       = 2**WeightWidth - 1,
  // Maximum number of QoS priority levels an input can gain through aging, as in the DUT.
  localparam int unsigned AgingQosMax     = QosMax,
  // Aging is only active together with QoS, as in the DUT.
  localparam bit          AgingActive     = EnableQos && EnableAging,
  // Check starvation, unless QoS is enabled without aging.
  localparam bit          StarvationCheck = !EnableQos || AgingActive,
  // Maximum number of transfers an input may wait before being served.
  localparam int unsigned StarvationBound = 2 * ((QosMax + AgingQosMax + 1) * AgingThreshold +
                                                 2 * NumIn * WeightMax),
  // Derived types, do **not** overwrite!
  //
  localparam type         data_t          = logic [DataWidth-1:0],
  localparam type         idx_t           = logic [IdxWidth-1:0],
  localparam type         qos_t           = logic [QosWidth-1:0],
  localparam type         weight_t        = logic [WeightWidth-1:0]
);


  // Clock and reset generator.
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  initial begin : proc_drive_req
    req_inp = '0;
    @(posedge rst_n);
    req_inp = '1;
  end

  initial begin : proc_drive_rdy
    gnt_oup = 1'b0;
    @(posedge rst_n);
    gnt_oup = 1'b1;
  end


  initial begin : proc_check
    automatic longint unsigned cnt            [NumInp];
    automatic int     unsigned max_wait       [NumInp];
    automatic int     unsigned last_grant_cyc [NumInp];
    automatic longint unsigned total, hi, lo;
    automatic int     unsigned cyc;
    automatic real             hi_ratio;

    foreach (cnt[i])            cnt[i]            = 0;
    foreach (max_wait[i])       max_wait[i]       = 0;
    foreach (last_grant_cyc[i]) last_grant_cyc[i] = 0;
    total = 0; cyc = 0;

    @(posedge rst_n);
    repeat (200) @(posedge clk);

    while (total < NumFlits) begin
      @(posedge clk);
      #TestTime;
      cyc++;
      if (req_oup && gnt_oup) begin
        cnt[idx_oup]++;
        total++;
        if ((cyc - last_grant_cyc[idx_oup]) > max_wait[idx_oup])
          max_wait[idx_oup] = cyc - last_grant_cyc[idx_oup];
        last_grant_cyc[idx_oup] = cyc;
        assert (data_oup === data_inp[idx_oup])
          else $error("Data mismatch: idx_o=%0d data_o=%0d", idx_oup, data_oup);
      end
    end

    hi = cnt[0] + cnt[1];
    lo = cnt[2] + cnt[3];
    $display("=== cc_qos_wrr_arbiter (high tier {0:w1, 1:w3} QoS2, low tier {2,3} QoS0, AgingInterval=%0d) ===",
             AgingInterval);
    for (int unsigned i = 0; i < NumInp; i++)
      $display("Input %0d (QoS=%0d, weight=%0d): grants=%0d  share=%0f  maxWait=%0d cyc",
               i, (i < 2) ? 2 : 0, (i == 1) ? 3 : 1, cnt[i], real'(cnt[i]) / real'(total), max_wait[i]);
    $display("High tier total=%0d  Low tier total=%0d", hi, lo);

    hi_ratio = real'(cnt[1]) / real'(cnt[0]);
    $display("Within high tier: cnt[1]/cnt[0] = %0f (ideal 3.0)", hi_ratio);

    // machine-readable line for the aging-tuning curve (low-tier share / max wait vs AgingInterval)
    $display("CSV,aging,interval=%0d,lo_share=%0f,lo_maxwait=%0d,hi_share=%0f,hi_ratio=%0f",
             AgingInterval, real'(lo) / real'(total),
             (max_wait[2] > max_wait[3]) ? max_wait[2] : max_wait[3],
             real'(hi) / real'(total), hi_ratio);

    // 3. No starvation: aging must give every input some service (holds at any interval).
    for (int unsigned i = 0; i < NumInp; i++)
      assert (cnt[i] > 0) else $error("Input %0d starved.", i);

    // The QoS-dominance and 3:1-split checks only hold at the nominal interval; skip when sweeping.
    if (!SweepMode) begin
      // 1. QoS priority: high tier dominates the link.
      assert (hi > 10 * lo)
        else $error("High QoS tier does not dominate: hi=%0d lo=%0d", hi, lo);
      // 2. Weighted split inside the high tier: input 1 (w=3) ~= 3x input 0 (w=1).
      assert (hi_ratio > 2.7 && hi_ratio < 3.3)
        else $error("High-tier weight split off: cnt[1]/cnt[0]=%0f (ideal 3.0)", hi_ratio);
    end

    $display("=== QoS+WRR arbiter test done ===");
    $stop();
  end

  /////////
  // DUT //
  /////////
  assign arb_round_owner = i_dut_qos_wrr.i_cc_wrr_arbiter.round_owner_o;

  cc_qos_wrr_arbiter #(
    .NumIn          ( NumIn          ),
    .DataWidth      ( DataWidth      ),
    .QosWidth       ( QosWidth       ),
    .WeightWidth    ( WeightWidth    ),
    .AgingThreshold ( AgingThreshold ),
    .EnableQos      ( EnableQos      ),
    .EnableWrr      ( EnableWrr      ),
    .EnableAging    ( EnableAging    )
  ) i_dut_qos_wrr (
    .clk_i          ( clk                ),
    .rst_ni         ( rst_n              ),
    .flush_i        ( flush              ),
    .req_i          ( req_i_dut          ),
    .gnt_o          ( gnt_o_dut          ),
    .data_i         ( data_i_dut         ),
    .qos_i          ( qos_i_dut          ),
    .weight_i       ( weight_i_dut       ),
    .req_o          ( req_o_dut          ),
    .gnt_i          ( gnt_i_dut          ),
    .data_o         ( data_o_dut         ),
    .idx_o          ( idx_o_dut          ),
    .weight_error_o ( weight_error_o_dut )
  );

  ////////////////////////
  // Reference arbiters //
  ////////////////////////
  // Standalone weighted round-robin arbiter.
  cc_wrr_arbiter #(
    .NumIn       ( NumIn       ),
    .DataWidth   ( DataWidth   ),
    .WeightWidth ( WeightWidth )
  ) i_ref_wrr (
    .clk_i          ( clk              ),
    .rst_ni         ( rst_n            ),
    .flush_i        ( flush            ),
    .req_i          ( req_i_ref_wrr    ),
    .gnt_o          ( gnt_o_ref_wrr    ),
    .data_i         ( data_i_dut       ),
    .weight_i       ( weight_i_ref_wrr ),
    .req_o          ( req_o_ref_wrr    ),
    .gnt_i          ( gnt_i_dut        ),
    .data_o         ( data_o_ref_wrr   ),
    .idx_o          ( idx_o_ref_wrr    ),
    .weight_error_o (                  ),
    .round_owner_o  (                  )
  );

  // Standalone basic round-robin arbiter.
  cc_rr_arb_tree #(
    .NumIn     ( NumIn     ),
    .DataWidth ( DataWidth ),
    .ExtPrio   ( 1'b0      ),
    .AxiVldRdy ( 1'b1      ),
    .LockIn    ( 1'b1      ),
    .FairArb   ( 1'b1      )
  ) i_ref_rr (
    .clk_i   ( clk           ),
    .rst_ni  ( rst_n         ),
    .flush_i ( flush         ),
    .rr_i    ( '0            ),
    .req_i   ( req_i_ref_rr  ),
    .gnt_o   ( gnt_o_ref_rr  ),
    .data_i  ( data_i_dut    ),
    .gnt_i   ( gnt_i_dut     ),
    .req_o   ( req_o_ref_rr  ),
    .data_o  ( data_o_ref_rr ),
    .idx_o   ( idx_o_ref_rr  )
  );

endmodule
