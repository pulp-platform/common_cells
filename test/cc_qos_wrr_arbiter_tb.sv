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
  // Number of input requests in a test, rounded up to be a multiple of the input weight during
  // tests.
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

  /////////////
  // Signals //
  /////////////
  // DUT interface.
  logic                 clk;
  logic                 rst_n;
  logic                 clr;
  logic    [NumIn-1:0]  req_i_dut;
  logic    [NumIn-1:0]  gnt_o_dut;
  data_t   [NumIn-1:0]  data_i_dut;
  qos_t    [NumIn-1:0]  qos_i_dut;
  weight_t [NumIn-1:0]  weight_i_dut;
  logic                 req_o_dut;
  logic                 gnt_i_dut;
  data_t                data_o_dut;
  idx_t                 idx_o_dut;
  logic    [NumIn-1:0]  weight_error_o_dut;

  // DUT TB.
  weight_t [NumIn-1:0]  weight_eff;

  // Reference arbiters.
  logic                 compare_ref_rr_en, compare_ref_wrr_en;
  logic    [NumIn-1:0]  req_i_ref_rr,      req_i_ref_wrr;
  logic    [NumIn-1:0]  gnt_o_ref_rr,      gnt_o_ref_wrr;
  weight_t [NumIn-1:0]  weight_i_ref_wrr;
  logic                 req_o_ref_rr,      req_o_ref_wrr;
  data_t                data_o_ref_rr,     data_o_ref_wrr;
  idx_t                 idx_o_ref_rr,      idx_o_ref_wrr;

  // Test configuration.
  string                test_name;
  bit                   compare_ref_rr;        // compare against `cc_rr_arb_tree` in lock-step
  bit                   compare_ref_wrr;       // compare against `cc_wrr_arbiter` in lock-step
  bit                   check_output_stable;   // check whether outputs change while stalled
  bit                   check_arb_round_order; // check whether arbitration is handled correctly
  int unsigned          stall_percent;         // backpressure probability (%)
  int unsigned          num_inputs_done;       // number of input drivers that sent all requests

  // Clear control.
  logic                 clr_test;              // clear between consecutive tests

  ////////////////////////
  // Signal assignments //
  ////////////////////////
  assign clr        = clr_test;
  assign weight_eff = EnableWrr ? weight_i_dut : {NumIn{weight_t'(1)}};

  assign compare_ref_rr_en  = compare_ref_rr  || (!EnableQos && !EnableWrr);
  assign compare_ref_wrr_en = compare_ref_wrr || !EnableQos;

  assign req_i_ref_rr     = req_i_dut & {NumIn{compare_ref_rr_en}};
  assign req_i_ref_wrr    = req_i_dut & {NumIn{compare_ref_wrr_en}};
  assign weight_i_ref_wrr = weight_eff;

  /////////////////////
  // Clock and reset //
  /////////////////////
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  /////////////
  // Stimuli //
  /////////////
  // Generate random data payload.
  function automatic data_t random_data();
    for (int unsigned i = 0; i < DataWidth; i++) begin
      random_data[i] = $urandom();
    end
  endfunction : random_data

  //////////////////
  // Test control //
  //////////////////
  // Inject one request on input `i` and hold it until its valid/ready handshake.
  task automatic send_tx(input int unsigned i, input qos_t qos);
    req_i_dut[i]  <= #ApplTime 1'b1;
    data_i_dut[i] <= #ApplTime random_data();
    qos_i_dut[i]  <= #ApplTime qos;
    #TestTime;
    while (!gnt_o_dut[i]) begin
      @(posedge clk);
      #TestTime;
    end
    @(posedge clk);
  endtask : send_tx

  // Withdraw the request on input `i` and keep the input idle for `cycles` cycles. With
  // `cycles = 0`, the request is only withdrawn.
  task automatic idle_tx(input int unsigned i, input int unsigned cycles);
    req_i_dut[i]  <= #ApplTime 1'b0;
    data_i_dut[i] <= #ApplTime '0;
    repeat (cycles) @(posedge clk);
  endtask : idle_tx

  // Set the input weights while all inputs are idle, and wait for them to apply.
  task automatic set_weights(input weight_t weights [NumIn]);
    for (int unsigned i = 0; i < NumIn; i++) weight_i_dut[i] <= #ApplTime weights[i];
    @(posedge clk);
  endtask : set_weights

  // Inject multiple requests on input `i` with priority level `qos`. A random idle time is
  // inserted between requests. By activating `random_qos`, each request carries a random
  // priority level instead of the input `qos`. The input weight is the number of requests served
  // in one arbitration round.
  task automatic drive_input(input int unsigned i, input qos_t qos, input int unsigned num_reqs,
                             input bit random_qos, input int unsigned max_idle);
    automatic int unsigned idle_cycles;
    automatic int unsigned num_rounds;
    // Round up the number of requests to a multiple of the weight.
    num_rounds = (num_reqs + weight_eff[i] - 1) / weight_eff[i];
    for (int unsigned j = 0; j < num_rounds * weight_eff[i]; j++) begin
      send_tx(i, random_qos ? qos_t'($urandom_range(0, QosMax)) : qos);
      idle_cycles = $urandom_range(0, max_idle);
      if (idle_cycles > 0) idle_tx(i, idle_cycles);
    end
    // Withdraw the last request, which is still asserted after its handshake.
    idle_tx(i, 0);
    num_inputs_done++;
  endtask : drive_input

  // Run all input drivers concurrently until every input sent its requests.
  task automatic run_input_drivers(input int unsigned num_reqs, input int unsigned max_idle,
                                   input bit random_qos, input qos_t qos [NumIn]);
    num_inputs_done = 0;
    for (int unsigned i = 0; i < NumIn; i++) begin
      fork
        automatic int unsigned k = i;
        drive_input(k, qos[k], num_reqs, random_qos, max_idle);
      join_none
    end
    wait fork;
    @(posedge clk);
  endtask : run_input_drivers

  // Separate two tests: let the output drain, then clear the DUT and the reference model.
  task automatic next_test(input string name);
    repeat (10) @(posedge clk);
    clr_test <= #ApplTime 1'b1;
    @(posedge clk);
    clr_test <= #ApplTime 1'b0;
    @(posedge clk);
    test_name = name;
    $display("[%0t] Test %s", $time, name);
  endtask : next_test

  // Calculate the index of the next round-robin input.
  function automatic int unsigned next_rr_input(input int unsigned idx);
    return (idx + 1) % NumIn;
  endfunction : next_rr_input

  ///////////////
  // DUT tests //
  ///////////////
  initial begin : proc_tests
    qos_t    qos [NumIn];
    weight_t weights [NumIn];

    // Initialization.
    test_name             = "reset";
    stall_percent         = 0;
    check_output_stable   = 1'b0;
    check_arb_round_order = 1'b0;
    compare_ref_rr        = 1'b0;
    compare_ref_wrr       = 1'b0;
    clr_test              = 1'b0;
    req_i_dut             = '0;
    data_i_dut            = '0;
    qos_i_dut             = '0;
    weight_i_dut          = {NumIn{weight_t'(1)}};
    @(posedge rst_n);
    @(posedge clk);

    // Test 1
    // This test assesses the back-compatibility with `cc_rr_arb_tree`, based on the same
    // tests in `cc_rr_arb_tree_tb` with a fixed input schedule and no backpressure.
    next_test("dut_vs_ref_rr_fixed_no_stall");
    // All inputs have the same weight, so weighted arbitration has no effect.
    foreach (weights[i]) weights[i] = weight_t'(1);
    set_weights(weights);
    // All inputs have the same QoS priority level, so QoS and aging have no effect.
    qos_i_dut <= #ApplTime {NumIn{qos_t'(QosMax / 2)}};
    @(posedge clk);
    // Activate comparison with reference arbiters.
    compare_ref_rr  = 1'b1;
    compare_ref_wrr = 1'b1;
    // No backpressure.
    stall_percent = 0;
    for (int unsigned i = 0; i < NumIn; i++) begin
      fork
        automatic int unsigned k = i;
        begin
          for (int unsigned j = 0; j < (k + 1) * NumReqs / 4; j++) begin
            req_i_dut[k]  <= #ApplTime 1'b1;
            data_i_dut[k] <= #ApplTime random_data();
            @(posedge clk);
          end
          idle_tx(k, (NumIn - k) * NumReqs / 4);
          for (int unsigned j = 0; j < NumReqs / 4; j++) begin
            req_i_dut[k]  <= #ApplTime (k % 2 == 0);
            data_i_dut[k] <= #ApplTime random_data();
            @(posedge clk);
          end
          idle_tx(k, 0);
        end
      join_none
    end
    wait fork;

    // Test 2
    // This test assesses the back-compatibility with `cc_rr_arb_tree`, using a random input
    // schedule and backpressure.
    next_test("dut_vs_ref_rr_random_stall");
    // Add backpressure.
    stall_percent       = 30;
    check_output_stable = 1'b1;
    foreach (qos[i]) qos[i] = qos_t'(QosMax / 2);
    run_input_drivers(NumReqs, 2 * NumIn, 1'b0, qos);

    // Test 3
    // This test assesses weighted round-robin arbitration against the standalone `cc_wrr_arbiter`,
    // using saturated inputs with equal QoS.
    next_test("dut_vs_ref_wrr_saturated_stall");
    // Use weights, so do not compare anymore with the reference round-robin arbiter.
    compare_ref_rr = 1'b0;
    for (int unsigned i = 0; i < NumIn; i++) begin
      weights[i] = weight_t'((i % WeightMax) + 1);
      qos[i]     = '0;
    end
    set_weights(weights);
    check_arb_round_order = (NumIn > 1);
    run_input_drivers(NumReqs, 0, 1'b0, qos);
    check_arb_round_order = 1'b0;

    // Test 4
    // This test assesses weighted round-robin arbitration against the standalone `cc_wrr_arbiter`,
    // using random traffic and random weights.
    next_test("dut_vs_ref_wrr_random_stall");
    for (int unsigned i = 0; i < NumIn; i++) begin
      weights[i] = weight_t'($urandom_range(1, WeightMax));
      qos[i]     = '0;
    end
    set_weights(weights);
    run_input_drivers(NumReqs, 3 * NumIn, 1'b0, qos);

    // Test 5
    // This test assesses QoS priority-aware arbitration and the aging mechanism, using saturated
    // inputs, two inputs per QoS priority level and different weights.
    next_test("dut_qos_aging_saturated_stall");
    compare_ref_wrr = 1'b0;
    for (int unsigned i = 0; i < NumIn; i++) begin
      weights[i] = weight_t'((i % 2) ? WeightMax : 1);
      qos[i]     = qos_t'(((i / 2) * QosMax) / ((NumIn > 2) ? (NumIn - 1) / 2 : 1));
    end
    set_weights(weights);
    run_input_drivers(NumReqs, 0, 1'b0, qos);

    // Test 6
    // This test assesses all the mechanisms of the DUT together.
    for (int unsigned r = 0; r < 4; r++) begin
      next_test($sformatf("dut_all_random_stall/%0d", r));
      for (int unsigned i = 0; i < NumIn; i++) begin
        weights[i] = weight_t'($urandom_range(1, WeightMax));
      end
      set_weights(weights);
      stall_percent = $urandom_range(0, 60);
      run_input_drivers(NumReqs / 2, 3 * NumIn, 1'b1, qos);
    end

    next_test("done");
    repeat (10) @(posedge clk);
    $display("cc_qos_wrr_arbiter_tb tests done");
    $stop();
  end

  //////////////////////////////////
  // Generate output backpressure //
  //////////////////////////////////
  initial begin : proc_gen_backpressure
    gnt_i_dut = 1'b0;
    @(posedge rst_n);
    forever begin
      gnt_i_dut <= #ApplTime ($urandom_range(0, 99) >= stall_percent);
      @(posedge clk);
    end
  end

  ///////////////////////
  // Validation checks //
  ///////////////////////
  initial begin : proc_tests_checks
    // Reference model.
    int unsigned      qos_aging [NumIn];
    int unsigned      qos_aging_cnt;
    bit               qos_aging_up;
    int unsigned      qos_eff [NumIn];
    int unsigned      qos_eff_max;
    logic [NumIn-1:0] qos_top_req, qos_req_d, qos_req_q;
    // Arbitration owner.
    int          owner_idx;
    // Number of remaining transfers.
    int unsigned owner_cnt;
    // Starvation counter.
    int unsigned starvation_cnt [NumIn];
    // Output stability.
    bit    stalled;
    idx_t  stall_idx;
    data_t stall_data;
    // Arbitration round.
    int               arb_round_idx;
    int unsigned      arb_round_len;
    bit               transfer;
    logic [NumIn-1:0] gnt_o_expected;

    // Initialization.
    foreach (qos_aging[i])      qos_aging[i]      = 0;
    foreach (starvation_cnt[i]) starvation_cnt[i] = 0;
    qos_req_q     = '0;
    owner_idx     = -1;
    owner_cnt     = 0;
    qos_aging_cnt = 0;
    stalled       = 1'b0;
    arb_round_idx = -1;
    arb_round_len = 0;

    @(posedge rst_n);
    forever begin
      @(posedge clk);
      #TestTime;
      transfer = req_o_dut && gnt_i_dut;

      // Check that the output grant is released for the correct input (one-hot).
      gnt_o_expected = '0;
      if (transfer) gnt_o_expected[idx_o_dut] = 1'b1;
      assert (gnt_o_dut === gnt_o_expected) else
        $error("[%s] gnt_o=%b, expected %b (req_o=%b gnt_i=%b idx_o=%0d)",
               test_name, gnt_o_dut, gnt_o_expected, req_o_dut, gnt_i_dut, idx_o_dut);

      // Check that the output channel is used by the input winning arbitration.
      if (req_o_dut) begin
        assert (req_i_dut[idx_o_dut]) else
          $error("[%s] req_o raised for idle input %0d", test_name, idx_o_dut);
        assert (data_o_dut === data_i_dut[idx_o_dut]) else
          $error("[%s] data_o=%h, expected %h from input %0d",
                 test_name, data_o_dut, data_i_dut[idx_o_dut], idx_o_dut);
      end

      // Check that `weight_error_o` flags exactly the inputs carrying a weight value of zero.
      for (int unsigned i = 0; i < NumIn; i++) begin
        assert (weight_error_o_dut[i] === (EnableWrr && (weight_i_dut[i] == '0))) else
          $error("[%s] weight_error_o[%0d]=%b with weight %0d", test_name, i, weight_error_o_dut[i],
                 weight_i_dut[i]);
      end

      // Check output stability under backpressure.
      if (check_output_stable && stalled && !clr) begin
        assert (req_o_dut && (idx_o_dut == stall_idx) && (data_o_dut === stall_data)) else
          $error("[%s] Output changed while stalled: req_o=%b idx_o=%0d (was %0d)",
                 test_name, req_o_dut, idx_o_dut, stall_idx);
      end

      // Calculate effective QoS priority level for each input using the reference model.
      qos_eff_max = 0;
      for (int unsigned i = 0; i < NumIn; i++) begin
        qos_eff[i] = (EnableQos ? qos_i_dut[i] : 0) + qos_aging[i];
        if (req_i_dut[i] && (qos_eff[i] > qos_eff_max)) qos_eff_max = qos_eff[i];
      end
      for (int unsigned i = 0; i < NumIn; i++) begin
        qos_top_req[i] = req_i_dut[i] && (qos_eff[i] == qos_eff_max);
      end
      qos_req_d = stalled ? (qos_req_q & req_i_dut) : qos_top_req;
      qos_req_q = qos_req_d;

      // Check that an arbitration round is never interrupted until the owner's last transfer.
      if (transfer) begin
        if (owner_cnt > 0) begin
          assert (idx_o_dut == owner_idx) else
            $error("[%s] Round of input %0d preempted by input %0d", test_name, owner_idx,
                   idx_o_dut);
        end

        // Check that the first transfer of a new arbitration round goes to an input with the
        // highest QoS priority level.
        if ((idx_o_dut == owner_idx) && (owner_cnt > 0)) begin
          owner_cnt--;
        end else begin
          assert (qos_req_d[idx_o_dut]) else
            $error("[%s] Round of input %0d at QoS %0d, below the highest QoS level %0d (%b)",
                   test_name, idx_o_dut, qos_eff[idx_o_dut], qos_eff_max, qos_req_d);
          owner_idx = idx_o_dut;
          owner_cnt = weight_eff[idx_o_dut] - 1;
        end
      end

      // Check that no input waits for more than `StarvationBound` transfers.
      for (int unsigned i = 0; i < NumIn; i++) begin
        if (!req_i_dut[i] || (transfer && (idx_o_dut == i)) || clr) begin
          starvation_cnt[i] = 0;
        end else if (transfer) begin
          starvation_cnt[i]++;
          assert (!StarvationCheck || (starvation_cnt[i] <= StarvationBound)) else
            $error("[%s] Input %0d waited for more than %0d transfers", test_name, i,
                   StarvationBound);
        end
      end

      // Check errors derived from the DUT comparison against the reference arbiter
      // `cc_rr_arb_tree`.
      if (compare_ref_rr_en) begin
        assert ((req_o_ref_rr === req_o_dut) && ((gnt_o_ref_rr & req_i_dut) === gnt_o_dut)) else
          $error("[%s] Mismatch with cc_rr_arb_tree: req_o=%b/%b gnt_o=%b/%b",
                 test_name, req_o_dut, req_o_ref_rr, gnt_o_dut, gnt_o_ref_rr & req_i_dut);
        if (req_o_dut) begin
          assert ((idx_o_ref_rr === idx_o_dut) && (data_o_ref_rr === data_o_dut)) else
            $error("[%s] Mismatch with cc_rr_arb_tree: idx_o=%0d/%0d", test_name, idx_o_dut,
                   idx_o_ref_rr);
        end
      end

      // Check errors derived from the DUT comparison against the reference arbiter
      // `cc_wrr_arbiter`.
      if (compare_ref_wrr_en) begin
        assert ((req_o_ref_wrr === req_o_dut) && (gnt_o_ref_wrr === gnt_o_dut)) else
          $error("[%s] Mismatch with cc_wrr_arbiter: req_o=%b/%b gnt_o=%b/%b",
                 test_name, req_o_dut, req_o_ref_wrr, gnt_o_dut, gnt_o_ref_wrr);
        if (req_o_dut) begin
          assert ((idx_o_ref_wrr === idx_o_dut) && (data_o_ref_wrr === data_o_dut)) else
            $error("[%s] Mismatch with cc_wrr_arbiter: idx_o=%0d/%0d", test_name, idx_o_dut,
                   idx_o_ref_wrr);
        end
      end

      // Check that each arbitration round matches the expected interval of time, proportional to
      // the input weight value. Check also that the round-robin arbiter serves inputs following
      // the expected ordering.
      if (!check_arb_round_order || (num_inputs_done > 0) || clr) begin
        arb_round_idx = -1;
      end else if (transfer) begin
        if (idx_o_dut == arb_round_idx) begin
          arb_round_len++;
          assert (arb_round_len <= weight_eff[idx_o_dut]) else
            $error("[%s] Round of input %0d longer than its weight %0d",
                   test_name, idx_o_dut, weight_eff[idx_o_dut]);
        end else begin
          if (arb_round_idx >= 0) begin
            assert (arb_round_len == weight_eff[arb_round_idx]) else
              $error("[%s] Round of input %0d lasted %0d transfers, expected %0d",
                     test_name, arb_round_idx, arb_round_len, weight_eff[arb_round_idx]);
            assert (idx_o_dut == next_rr_input(arb_round_idx)) else
              $error("[%s] Input %0d served after input %0d, expected input %0d",
                     test_name, idx_o_dut, arb_round_idx, next_rr_input(arb_round_idx));
          end
          arb_round_idx = idx_o_dut;
          arb_round_len = 1;
        end
      end

      // Update the reference model.
      stalled      = req_o_dut && !gnt_i_dut && !clr;
      stall_idx    = idx_o_dut;
      stall_data   = data_o_dut;
      qos_aging_up = transfer && ((AgingThreshold <= 1) || (qos_aging_cnt == AgingThreshold - 1));
      if (clr) begin
        qos_aging_cnt = 0;
        owner_cnt     = 0;
        foreach (qos_aging[i]) qos_aging[i] = 0;
      end else begin
        if (transfer) qos_aging_cnt = qos_aging_up ? 0 : qos_aging_cnt + 1;
        for (int unsigned i = 0; i < NumIn; i++) begin
          if ((transfer && (idx_o_dut == i)) || !req_i_dut[i]) begin
            qos_aging[i] = 0;
          end else if (AgingActive && !qos_top_req[i] && qos_aging_up &&
                       (qos_aging[i] < AgingQosMax)) begin
            qos_aging[i]++;
          end
        end
      end
    end
  end

  final begin
    $display("Tests completed up to: %s", test_name);
  end

  /////////
  // DUT //
  /////////
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
    .clr_i          ( clr                ),
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
    .clr_i          ( clr              ),
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
    .clr_i   ( clr           ),
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
