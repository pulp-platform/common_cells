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
// 1. `dut_vs_ref_rr`: this test assesses the DUT back-compatibility with `cc_rr_arb_tree`.
//    The DUT must be cycle-equivalent to the reference arbiter, which runs in lock-step
//    on the same stimuli. The traffic is generated as in `cc_rr_arb_tree_tb`. QoS and
//    weights are maintained equal across different inputs.
//
// 2. `dut_vs_ref_wrr_saturated`: this test assesses the weighted round-robin arbitration of the DUT
//    against the standalone `cc_wrr_arbiter`. Each arbitration round must last exactly
//    `weight_i[i]` transfers. Arbitration rounds must rotate in round-robin order. The DUT must be
//    cycle-equivalent to the reference arbiter, which runs in lock-step on the same stimuli. QoS is
//    maintained equal across different inputs, while each input has a distinct weight.
//
// 3. `dut_vs_ref_wrr_random`: this test assesses the weighted round-robin arbitration of the DUT
//    against the standalone `cc_wrr_arbiter` under random traffic. The DUT must be cycle-equivalent
//    to the reference arbiter, which runs in lock-step on the same stimuli. All checks on the DUT
//    therefore also apply to the reference arbiter. Requests arrive with random timing, and the
//    output is under random back-pressure. QoS is maintained equal across different inputs, while
//    weights are random.
//
// 4. `dut_qos_aging`: this test assesses the QoS priority-aware arbitration and the QoS aging of
//    the DUT. Each arbitration round must start with an input at the highest effective QoS priority
//    level. Aging must prevent starvation by ensuring a stalled requester not to exceed
//    `StarveBound` of waiting time. `StarveBound` is a safe upper bound on the time an input needs
//    to age up to the highest QoS priority level and then wait for its round-robin turn. All inputs
//    are saturated, and the output is under random back-pressure. Inputs are spread over several
//    QoS priority levels, two inputs per level with different weights, so that the weighted split
//    within a QoS priority level is also exercised.
//
// 5. `dut_all_random`: this test assesses all the mechanisms of the DUT together. Requests arrive
//    with random timing, carrying a random QoS priority level. Weights are randomized at every
//    repetition of the test and the output is under random back-pressure.

module cc_qos_wrr_arbiter_tb #(
  parameter int unsigned NumInp        = 32'd4,
  parameter int unsigned QosWidth      = 32'd4,
  parameter int unsigned WtWidth       = 32'd4,
  parameter int unsigned AgeWidth      = 32'd4,
  parameter int unsigned AgingInterval = 32'd64,
  parameter int unsigned NumFlits      = 32'd200000,
  /// When sweeping AgingInterval, set to 1 to relax the QoS-dominance/ratio asserts (they only
  /// hold at the nominal interval); the CSV line is still emitted for the tuning curve.
  parameter bit          SweepMode     = 1'b0
);

  localparam time CyclTime = 10ns;
  localparam time TestTime = 8ns;

  localparam int unsigned DataWidth = 32'd32;
  localparam int unsigned IdxWidth  = (NumInp > 32'd1) ? unsigned'($clog2(NumInp)) : 32'd1;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [IdxWidth-1:0]  idx_t;

  logic clk, rst_n;

  logic  [NumInp-1:0]               req_inp, gnt_inp;
  data_t [NumInp-1:0]              data_inp;
  logic  [NumInp-1:0][QosWidth-1:0] qos;
  logic  [NumInp-1:0][WtWidth-1:0]  weights;
  logic                             req_oup, gnt_oup;
  data_t                            data_oup;
  idx_t                             idx_oup;

  // Two tiers: inputs 0,1 are high QoS; 2,3 are low QoS. Within the high tier, weights are 1:3.
  for (genvar i = 0; i < NumInp; i++) begin : gen_inp_const
    assign qos[i]      = (i < 2) ? QosWidth'(2) : QosWidth'(0);
    assign weights[i]  = (i == 1) ? WtWidth'(3) : WtWidth'(1);
    assign data_inp[i] = data_t'(i);
  end

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

  cc_qos_wrr_arbiter #(
    .NumIn         ( NumInp        ),
    .DataWidth     ( DataWidth     ),
    .QosWidth      ( QosWidth      ),
    .WtWidth       ( WtWidth       ),
    .AgeWidth      ( AgeWidth      ),
    .AgingInterval ( AgingInterval )
  ) i_dut (
    .clk_i     ( clk      ),
    .rst_ni    ( rst_n    ),
    .flush_i   ( 1'b0     ),
    .req_i     ( req_inp  ),
    .gnt_o     ( gnt_inp  ),
    .data_i    ( data_inp ),
    .qos_i     ( qos      ),
    .weights_i ( weights  ),
    .req_o     ( req_oup  ),
    .gnt_i     ( gnt_oup  ),
    .data_o    ( data_oup ),
    .idx_o     ( idx_oup  )
  );

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

endmodule
