// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Philippe Sauter <phsauter@iis.ee.ethz.ch>
//
// Description: Clearable Two-Phase CDC Testbench
// Exercise payload ordering, clear/isolate sequencing, async-reset behavior,
// and timed async-channel delay sweeps for cc_cdc_2phase_clearable.

// ----------------------------------------------------------------------------
// Monitor Error Package
// ----------------------------------------------------------------------------

package cc_cdc_2phase_clearable_tb_monitor_pkg;
  int unsigned monitor_errors = 0;

  task automatic report_monitor_error(input string msg);
    monitor_errors++;
    $error("%s", msg);
  endtask
endpackage

module cc_cdc_2phase_clearable_tb;

  timeunit 1ns;
  timeprecision 1ps;

  // --------------------------------------------------------------------------
  // Configuration
  // --------------------------------------------------------------------------
  parameter int unsigned NUM_RANDOM_TRANSFERS = 200;
  parameter int unsigned NUM_ACTIVE_STRESS_TRANSFERS = 160;
  parameter int unsigned NUM_ACTIVE_STRESS_EVENTS = 8;
  parameter int unsigned SYNC_STAGES = 3;
  parameter int unsigned TCK_SRC_PS = 10000;
  parameter int unsigned TCK_DST_PS = 17000;
  parameter int unsigned TIMEOUT_CYCLES = 20000;
  parameter int unsigned SEED = 32'hcdc2_c1ea;
  parameter bit          CLEAR_ON_ASYNC_RESET = 1'b1;
  parameter bit          INJECT_DELAYS = 1'b0;
  parameter int unsigned MAX_DELAY_PS = 0;
  parameter int unsigned SRC_START_DELAY_PS = 0;
  parameter int unsigned DST_START_DELAY_PS = 0;

  typedef enum logic [1:0] {
    DstReadyLow,
    DstReadyHigh,
    DstReadyRandom
  } dst_ready_mode_e;

  typedef enum logic [2:0] {
    EventSrcClear,
    EventDstClear,
    EventBothClear,
    EventSrcReset,
    EventDstReset
  } control_event_e;

  time tck_src = TCK_SRC_PS * 1ps;
  time tck_dst = TCK_DST_PS * 1ps;

  logic        src_rst_ni = 1'b1;
  logic        src_clk_i = 1'b0;
  logic        src_clear_i = 1'b0;
  logic        src_clear_pending_o;
  logic [31:0] src_data_i = '0;
  logic        src_valid_i = 1'b0;
  logic        src_ready_o;

  logic        dst_rst_ni = 1'b1;
  logic        dst_clk_i = 1'b0;
  logic        dst_clear_i = 1'b0;
  logic        dst_clear_pending_o;
  logic [31:0] dst_data_o;
  logic        dst_valid_o;
  logic        dst_ready_i = 1'b0;

  logic [31:0] expected_q[$];
  // Transactions accepted before/during a clear window may either be dropped or
  // complete later. They are still checked against this queue to catch truly
  // spurious or duplicated destination handshakes.
  logic [31:0] stale_q[$];
  int unsigned num_src_handshakes = 0;
  int unsigned num_dst_handshakes = 0;
  int unsigned num_stale_ignored = 0;
  int unsigned num_active_stress_events = 0;
  int unsigned num_errors = 0;
  bit          drop_window = 1'b0;
  bit          active_src_pause = 1'b0;
  bit          active_src_done = 1'b1;

  dst_ready_mode_e dst_ready_mode = DstReadyLow;

  // --------------------------------------------------------------------------
  // DUT Selection
  // --------------------------------------------------------------------------
  // Instantiate either the plain DUT or the timed delay-injection harness used
  // by sweeps to perturb every explicit asynchronous channel.
  if (INJECT_DELAYS) begin : gen_delayed_dut
    cc_cdc_2phase_clearable_tb_delay_injector #(
      .SYNC_STAGES          ( SYNC_STAGES          ),
      .CLEAR_ON_ASYNC_RESET ( CLEAR_ON_ASYNC_RESET ),
      .MAX_DELAY_PS         ( MAX_DELAY_PS         )
    ) i_dut (
      .src_rst_ni,
      .src_clk_i,
      .src_clear_i,
      .src_clear_pending_o,
      .src_data_i,
      .src_valid_i,
      .src_ready_o,
      .dst_rst_ni,
      .dst_clk_i,
      .dst_clear_i,
      .dst_clear_pending_o,
      .dst_data_o,
      .dst_valid_o,
      .dst_ready_i
    );
  end else begin : gen_dut
    cc_cdc_2phase_clearable #(
      .data_t            ( logic [31:0]        ),
      .SyncStages        ( SYNC_STAGES         ),
      .ClearOnAsyncReset ( CLEAR_ON_ASYNC_RESET )
    ) i_dut (
      .src_rst_ni,
      .src_clk_i,
      .src_clear_i,
      .src_clear_pending_o,
      .src_data_i,
      .src_valid_i,
      .src_ready_o,
      .dst_rst_ni,
      .dst_clk_i,
      .dst_clear_i,
      .dst_clear_pending_o,
      .dst_data_o,
      .dst_valid_o,
      .dst_ready_i
    );
  end

  // --------------------------------------------------------------------------
  // Clock And Ready Generation
  // --------------------------------------------------------------------------
  initial begin : gen_src_clk
    #(SRC_START_DELAY_PS * 1ps);
    forever #(tck_src / 2) src_clk_i = ~src_clk_i;
  end

  initial begin : gen_dst_clk
    #(DST_START_DELAY_PS * 1ps);
    forever #(tck_dst / 2) dst_clk_i = ~dst_clk_i;
  end

  always @(negedge dst_clk_i) begin
    case (dst_ready_mode)
      DstReadyLow:    dst_ready_i <= 1'b0;
      DstReadyHigh:   dst_ready_i <= 1'b1;
      DstReadyRandom: dst_ready_i <= ($urandom_range(0, 99) < 70);
      default:        dst_ready_i <= 1'b0;
    endcase
  end

  // --------------------------------------------------------------------------
  // Scoreboard And Protocol Checks
  // --------------------------------------------------------------------------
  // Scoreboard source and destination handshakes. During clear/reset windows,
  // accepted source items are stale: they may later complete or be dropped.
  always @(posedge src_clk_i) begin
    if (!src_rst_ni) begin
      // Reset is handled by the DUT. The scoreboard is controlled by the test
      // sequence because one-sided reset intentionally drops in-flight items.
    end else begin
      if (src_clear_pending_o && src_ready_o) begin
        report_error("src_ready_o asserted while src_clear_pending_o is asserted");
      end
      if (src_valid_i && src_ready_o) begin
        num_src_handshakes++;
        if (drop_window) begin
          stale_q.push_back(src_data_i);
        end else begin
          expected_q.push_back(src_data_i);
        end
      end
    end
  end

  always @(posedge dst_clk_i) begin
    logic [31:0] expected;

    if (!dst_rst_ni) begin
      // See source-side reset comment above.
    end else begin
      if (dst_clear_pending_o && dst_valid_o) begin
        report_error("dst_valid_o asserted while dst_clear_pending_o is asserted");
      end
      if (dst_valid_o && dst_ready_i) begin
        num_dst_handshakes++;
        if (consume_stale(dst_data_o)) begin
          num_stale_ignored++;
        end else if (drop_window) begin
          report_error($sformatf("unexpected destination transaction during drop window: data=0x%08h stale_pending=%0d",
                                 dst_data_o, stale_q.size()));
        end else if (expected_q.size() == 0) begin
          report_error($sformatf("unexpected destination transaction: data=0x%08h", dst_data_o));
        end else begin
          expected = expected_q.pop_front();
          if (dst_data_o !== expected) begin
            report_error($sformatf("transaction mismatch: expected=0x%08h actual=0x%08h",
                                   expected, dst_data_o));
          end
        end
      end
    end
  end

  // --------------------------------------------------------------------------
  // Test Helpers
  // --------------------------------------------------------------------------
  // Small shared helpers for reporting, cycle waits, and the stale-item window
  // used whenever a clear/reset may intentionally discard in-flight traffic.
  task automatic report_error(input string msg);
    num_errors++;
    $error("%s", msg);
  endtask

  function automatic bit consume_stale(input logic [31:0] data);
    int match_idx;

    match_idx = -1;
    foreach (stale_q[i]) begin
      if ((match_idx < 0) && (stale_q[i] === data)) begin
        match_idx = int'(i);
      end
    end

    if (match_idx < 0) begin
      return 1'b0;
    end

    // Earlier stale items may have been dropped by the clear sequence.
    repeat (match_idx + 1) begin
      void'(stale_q.pop_front());
    end
    return 1'b1;
  endfunction

  task automatic wait_src_cycles(input int unsigned cycles);
    repeat (cycles) begin
      @(posedge src_clk_i);
    end
    #1ps;
  endtask

  task automatic wait_dst_cycles(input int unsigned cycles);
    repeat (cycles) begin
      @(posedge dst_clk_i);
    end
    #1ps;
  endtask

  task automatic begin_drop_window;
    drop_window = 1'b1;
    while (expected_q.size() != 0) begin
      stale_q.push_back(expected_q.pop_front());
    end
  endtask

  task automatic reset_both_domains;
    drop_window = 1'b1;
    expected_q.delete();
    stale_q.delete();
    src_valid_i = 1'b0;
    src_clear_i = 1'b0;
    dst_clear_i = 1'b0;
    active_src_pause = 1'b0;
    active_src_done = 1'b1;
    dst_ready_mode = DstReadyLow;
    src_rst_ni = 1'b0;
    dst_rst_ni = 1'b0;

    fork
      wait_src_cycles(4);
      wait_dst_cycles(4);
    join

    src_rst_ni = 1'b1;
    dst_rst_ni = 1'b1;

    fork
      wait_src_cycles(6);
      wait_dst_cycles(6);
    join

    drop_window = 1'b0;
  endtask

  // --------------------------------------------------------------------------
  // Clear And Reset Helpers
  // --------------------------------------------------------------------------
  // Clear/reset completion helpers. They check that both domains see the
  // pending sequence and then wait for the CDC to settle before fresh traffic.
  task automatic wait_pending_seen(input bit expect_src, input bit expect_dst, input string test_name);
    bit seen_src;
    bit seen_dst;

    seen_src = !expect_src;
    seen_dst = !expect_dst;

    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (src_clear_pending_o) begin
        seen_src = 1'b1;
      end
      if (dst_clear_pending_o) begin
        seen_dst = 1'b1;
      end
      if (seen_src && seen_dst) begin
        return;
      end
      @(posedge src_clk_i or posedge dst_clk_i);
    end

    report_error($sformatf("timeout waiting for clear pending assertion in %s", test_name));
  endtask

  task automatic wait_clear_done(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (src_rst_ni && dst_rst_ni &&
          !src_clear_i && !dst_clear_i &&
          !src_clear_pending_o && !dst_clear_pending_o) begin
        fork
          wait_src_cycles(SYNC_STAGES + 4);
          wait_dst_cycles(SYNC_STAGES + 4);
        join
        expected_q.delete();
        return;
      end
      @(posedge src_clk_i or posedge dst_clk_i);
    end

    report_error($sformatf("timeout waiting for clear completion in %s", test_name));
  endtask

  // --------------------------------------------------------------------------
  // Traffic Helpers
  // --------------------------------------------------------------------------
  task automatic send_word(input logic [31:0] data);
    src_data_i = data;
    src_valid_i = 1'b1;

    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      @(negedge src_clk_i);
      if (src_ready_o) begin
        @(posedge src_clk_i);
        @(negedge src_clk_i);
        src_valid_i = 1'b0;
        src_data_i = '0;
        return;
      end
    end

    report_error($sformatf("timeout sending data=0x%08h", data));
    src_valid_i = 1'b0;
  endtask

  // Transfer helpers for normal traffic: send ordered words, wait for the
  // scoreboard to drain, and verify the source has returned to ready.
  task automatic wait_scoreboard_empty(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (expected_q.size() == 0) begin
        return;
      end
      @(posedge dst_clk_i or posedge src_clk_i);
    end

    report_error($sformatf("timeout waiting for scoreboard to drain in %s, pending=%0d",
                           test_name, expected_q.size()));
  endtask

  task automatic wait_src_ready(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (src_ready_o) begin
        return;
      end
      @(posedge src_clk_i or posedge dst_clk_i);
    end

    report_error($sformatf("timeout waiting for source ready in %s", test_name));
  endtask

  task automatic wait_dst_valid(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (dst_valid_o) begin
        return;
      end
      @(posedge dst_clk_i or posedge src_clk_i);
    end

    report_error($sformatf("timeout waiting for destination valid in %s", test_name));
  endtask

  task automatic send_sequence(input int unsigned num_words, input logic [31:0] base);
    for (int unsigned i = 0; i < num_words; i++) begin
      send_word(base + i);
      if ($urandom_range(0, 3) == 0) begin
        wait_src_cycles($urandom_range(1, 3));
      end
    end
  endtask

  // --------------------------------------------------------------------------
  // Control Event Helpers
  // --------------------------------------------------------------------------
  function automatic string control_event_name(input control_event_e ctrl_event);
    unique case (ctrl_event)
      EventSrcClear: control_event_name = "source synchronous clear";
      EventDstClear: control_event_name = "destination synchronous clear";
      EventBothClear: control_event_name = "simultaneous synchronous clear";
      EventSrcReset: control_event_name = "source asynchronous reset";
      EventDstReset: control_event_name = "destination asynchronous reset";
      default: control_event_name = "unknown control event";
    endcase
  endfunction

  function automatic bit event_touches_source(input control_event_e ctrl_event);
    return ctrl_event inside {EventSrcClear, EventBothClear, EventSrcReset};
  endfunction

  task automatic pulse_control_event(input control_event_e ctrl_event);
    unique case (ctrl_event)
      EventSrcClear: begin
        @(negedge src_clk_i);
        src_clear_i = 1'b1;
        @(negedge src_clk_i);
        src_clear_i = 1'b0;
      end
      EventDstClear: begin
        @(negedge dst_clk_i);
        dst_clear_i = 1'b1;
        @(negedge dst_clk_i);
        dst_clear_i = 1'b0;
      end
      EventBothClear: begin
        fork
          begin
            @(negedge src_clk_i);
            src_clear_i = 1'b1;
            @(negedge src_clk_i);
            src_clear_i = 1'b0;
          end
          begin
            @(negedge dst_clk_i);
            dst_clear_i = 1'b1;
            @(negedge dst_clk_i);
            dst_clear_i = 1'b0;
          end
        join
      end
      EventSrcReset: begin
        #(tck_src / 3);
        src_rst_ni = 1'b0;
        wait_src_cycles(2);
        src_rst_ni = 1'b1;
      end
      EventDstReset: begin
        #(tck_dst / 3);
        dst_rst_ni = 1'b0;
        wait_dst_cycles(2);
        dst_rst_ni = 1'b1;
      end
      default: begin
      end
    endcase
  endtask

  // Run a control event with the expected cross-domain clear sequence. The drop
  // window covers accepted items that may be intentionally discarded.
  task automatic run_control_event(input control_event_e ctrl_event, input string test_name,
                                   input bit pause_source_driver = 1'b0);
    if (pause_source_driver) begin
      pause_active_source(test_name);
    end

    begin_drop_window();
    if (event_touches_source(ctrl_event)) begin
      src_valid_i = 1'b0;
    end

    pulse_control_event(ctrl_event);
    wait_pending_seen(1'b1, 1'b1, test_name);
    wait_clear_done(test_name);
    drop_window = 1'b0;

    if (pause_source_driver) begin
      resume_active_source();
    end
  endtask

  task automatic check_no_cross_clear_after_reset(input control_event_e ctrl_event,
                                                  input string test_name);
    $display("%m: %s", test_name);
    src_valid_i = 1'b0;
    wait_scoreboard_empty(test_name);
    wait_src_ready(test_name);

    pulse_control_event(ctrl_event);

    for (int unsigned i = 0; i < TIMEOUT_CYCLES / 20; i++) begin
      unique case (ctrl_event)
        EventSrcReset: begin
          if (dst_clear_pending_o) begin
            report_error($sformatf("unexpected destination clear pending in %s", test_name));
            wait_clear_done(test_name);
            return;
          end
        end
        EventDstReset: begin
          if (src_clear_pending_o) begin
            report_error($sformatf("unexpected source clear pending in %s", test_name));
            wait_clear_done(test_name);
            return;
          end
        end
        default: begin
          report_error($sformatf("unsupported no-cross-clear event in %s", test_name));
          return;
        end
      endcase
      @(posedge src_clk_i or posedge dst_clk_i);
    end
  endtask

  // --------------------------------------------------------------------------
  // Transfer And Backpressure Scenarios
  // --------------------------------------------------------------------------
  task automatic run_transfer_check(input string test_name, input int unsigned num_words,
                                    input logic [31:0] base,
                                    input dst_ready_mode_e ready_mode);
    $display("%m: %s", test_name);
    dst_ready_mode = ready_mode;
    send_sequence(num_words, base);
    wait_scoreboard_empty(test_name);
    wait_src_ready(test_name);
    dst_ready_mode = DstReadyLow;
    wait_dst_cycles(2);
  endtask

  task automatic stage_backpressured_item(input logic [31:0] data, input string test_name);
    dst_ready_mode = DstReadyHigh;
    wait_src_ready(test_name);
    send_word(data);
    dst_ready_mode = DstReadyLow;
    wait_dst_valid(test_name);
  endtask

  // Backpressure tests stage one valid destination item, withhold ready, and
  // then trigger clear/reset to exercise the exposed valid-withdrawal contract.
  task automatic run_backpressured_control_check(input control_event_e ctrl_event,
                                                 input logic [31:0] staged_data,
                                                 input logic [31:0] post_base);
    string event_name;

    event_name = control_event_name(ctrl_event);
    $display("%m: %s while destination holds a valid item", event_name);
    stage_backpressured_item(staged_data,
                             {event_name, " while valid is backpressured"});
    run_control_event(ctrl_event, {event_name, " while valid is backpressured"});
    run_transfer_check({"post-", event_name, "-backpressure transfer"}, 8, post_base,
                       DstReadyHigh);
  endtask

  // --------------------------------------------------------------------------
  // Active Stress Scenario
  // --------------------------------------------------------------------------
  // Active-traffic stress keeps a source driver running while randomized
  // clear/reset events interrupt the CDC from either side.
  task automatic pause_active_source(input string test_name);
    active_src_pause = 1'b1;
    wait_src_cycles(2);
    @(negedge src_clk_i);
    #1ps;
    src_valid_i = 1'b0;
    src_data_i = '0;
    $display("%m: active source paused for %s", test_name);
  endtask

  task automatic resume_active_source;
    @(negedge src_clk_i);
    active_src_pause = 1'b0;
  endtask

  task automatic drive_active_source(input int unsigned num_words, input logic [31:0] base);
    int unsigned sent;
    bit handshake_seen;

    sent = 0;
    handshake_seen = 1'b0;
    active_src_done = 1'b0;
    src_valid_i = 1'b0;
    src_data_i = '0;

    while (sent < num_words) begin
      @(negedge src_clk_i);
      #1ps;

      if (!src_rst_ni || active_src_pause) begin
        src_valid_i = 1'b0;
        src_data_i = '0;
        handshake_seen = 1'b0;
      end else if (handshake_seen) begin
        handshake_seen = 1'b0;
        if ((sent >= num_words) || ($urandom_range(0, 9) == 0)) begin
          src_valid_i = 1'b0;
          src_data_i = '0;
        end else begin
          src_valid_i = 1'b1;
          src_data_i = base + sent;
        end
      end else if (!src_valid_i && ($urandom_range(0, 3) != 0)) begin
        src_valid_i = 1'b1;
        src_data_i = base + sent;
      end

      @(posedge src_clk_i);
      if (src_rst_ni && !active_src_pause && src_valid_i && src_ready_o) begin
        sent++;
        handshake_seen = 1'b1;
      end
    end

    @(negedge src_clk_i);
    src_valid_i = 1'b0;
    src_data_i = '0;
    active_src_done = 1'b1;
  endtask

  task automatic wait_active_event_gap;
    repeat ($urandom_range(4, 20)) begin
      @(posedge src_clk_i or posedge dst_clk_i);
    end
    #1ps;
  endtask

  task automatic run_active_control_events(input int unsigned num_events);
    string event_name;
    control_event_e ctrl_event;

    for (int unsigned i = 0; i < num_events; i++) begin
      wait_active_event_gap();
      if (CLEAR_ON_ASYNC_RESET) begin
        unique case (i)
          0: ctrl_event = EventDstClear;
          1: ctrl_event = EventDstReset;
          2: ctrl_event = EventSrcClear;
          3: ctrl_event = EventSrcReset;
          4: ctrl_event = EventBothClear;
          default: ctrl_event = control_event_e'($urandom_range(0, 4));
        endcase
      end else begin
        unique case (i)
          0: ctrl_event = EventDstClear;
          1: ctrl_event = EventSrcClear;
          2: ctrl_event = EventBothClear;
          default: ctrl_event = control_event_e'($urandom_range(0, 2));
        endcase
      end

      event_name = $sformatf("active stress event %0d: %s", i, control_event_name(ctrl_event));
      run_control_event(ctrl_event, event_name, event_touches_source(ctrl_event));

      num_active_stress_events++;
    end
  endtask

  task automatic run_active_traffic_stress;
    if ((NUM_ACTIVE_STRESS_TRANSFERS == 0) || (NUM_ACTIVE_STRESS_EVENTS == 0)) begin
      return;
    end

    $display("%m: active traffic stress: transfers=%0d events=%0d",
             NUM_ACTIVE_STRESS_TRANSFERS, NUM_ACTIVE_STRESS_EVENTS);
    expected_q.delete();
    stale_q.delete();
    drop_window = 1'b0;
    active_src_pause = 1'b0;
    active_src_done = 1'b0;
    dst_ready_mode = DstReadyRandom;

    fork
      drive_active_source(NUM_ACTIVE_STRESS_TRANSFERS, 32'ha000_0000);
      run_active_control_events(NUM_ACTIVE_STRESS_EVENTS);
    join

    if (!active_src_done) begin
      report_error("active source driver did not finish");
    end

    wait_scoreboard_empty("active traffic stress");
    wait_src_ready("active traffic stress");
    dst_ready_mode = DstReadyLow;
    wait_dst_cycles(2);
  endtask

  // --------------------------------------------------------------------------
  // Test Sequence
  // --------------------------------------------------------------------------
  initial begin : run_tests
    int unsigned seed;

    seed = SEED;
    seed = $urandom(seed);
    $display("%m: SEED=0x%08h derived=0x%08h", SEED, seed);

    reset_both_domains();

    // Baseline ordered transfer with the destination always ready.
    run_transfer_check("basic fixed-ready transfer", 32, 32'h1000_0000, DstReadyHigh);

    // Idle synchronous clears from source, destination, and both domains,
    // followed by fresh transfers to check post-clear recovery.
    run_control_event(EventSrcClear, "source synchronous idle clear");
    run_transfer_check("post-source-clear transfer", 16, 32'h2000_0000, DstReadyHigh);

    run_control_event(EventDstClear, "destination synchronous idle clear");
    run_transfer_check("post-destination-clear transfer", 16, 32'h3000_0000, DstReadyHigh);

    run_control_event(EventBothClear, "simultaneous synchronous idle clear");
    run_transfer_check("post-simultaneous-clear transfer", 16, 32'h4000_0000, DstReadyHigh);

    // One-sided asynchronous resets are only a cross-domain clear source when
    // the feature is enabled.
    if (CLEAR_ON_ASYNC_RESET) begin
      run_control_event(EventSrcReset, "source asynchronous idle reset");
      run_transfer_check("post-source-async-reset transfer", 16, 32'h5000_0000, DstReadyHigh);

      run_control_event(EventDstReset, "destination asynchronous idle reset");
      run_transfer_check("post-destination-async-reset transfer", 16, 32'h6000_0000, DstReadyHigh);
    end else begin
      check_no_cross_clear_after_reset(EventSrcReset,
                                       "source asynchronous idle reset without cross-clear");
      reset_both_domains();

      check_no_cross_clear_after_reset(EventDstReset,
                                       "destination asynchronous idle reset without cross-clear");
      reset_both_domains();
    end

    // Backpressured destination-visible traffic is the critical case where
    // clear/reset may withdraw valid and drop the staged item.
    run_backpressured_control_check(EventDstClear, 32'hc1ea_0001, 32'hc1ea_1000);
    run_backpressured_control_check(EventSrcClear, 32'hc1ea_2001, 32'hc1ea_3000);
    run_backpressured_control_check(EventBothClear, 32'hc1ea_4001, 32'hc1ea_5000);
    if (CLEAR_ON_ASYNC_RESET) begin
      run_backpressured_control_check(EventSrcReset, 32'hc1ea_6001, 32'hc1ea_7000);
      run_backpressured_control_check(EventDstReset, 32'hc1ea_8001, 32'hc1ea_9000);
    end

    // Long mixed stress run with random traffic, destination backpressure, and
    // interleaved source/destination clear or reset events.
    run_active_traffic_stress();

    // Final randomized-ready transfer checks ordinary payload ordering after
    // all disruptive control-event categories have completed.
    run_transfer_check("randomized ready transfer", NUM_RANDOM_TRANSFERS, 32'h7000_0000,
                       DstReadyRandom);

    if ((num_errors != 0) ||
        (cc_cdc_2phase_clearable_tb_monitor_pkg::monitor_errors != 0)) begin
      $fatal(1, "%m: failed with %0d testbench errors and %0d monitor errors",
             num_errors, cc_cdc_2phase_clearable_tb_monitor_pkg::monitor_errors);
    end

    $display("%m: passed: src_handshakes=%0d dst_handshakes=%0d stale_ignored=%0d stale_dropped=%0d active_stress_events=%0d",
             num_src_handshakes, num_dst_handshakes, num_stale_ignored,
             stale_q.size(), num_active_stress_events);
    $finish;
  end

  // --------------------------------------------------------------------------
  // Monitor Bindings
  // --------------------------------------------------------------------------
  // Bind a simulation-only monitor into each reset-controller half. It mirrors
  // the formal invariants to catch invalid internal clear FSM behavior in Questa.
  bind cc_cdc_reset_ctrlr_half cc_cdc_reset_ctrlr_half_monitor i_monitor (
    .clk_i,
    .rst_ni,
    .isolate_o,
    .isolate_ack_i,
    .clear_o,
    .clear_ack_i,
    .async_next_phase_o,
    .async_req_o,
    .async_next_phase_i,
    .async_req_i,
    .initiator_state_q,
    .initiator_clear_seq_phase,
    .initiator_phase_transition_req,
    .initiator_isolate_out,
    .initiator_clear_out,
    .receiver_phase_q,
    .receiver_effective_phase,
    .receiver_next_phase,
    .receiver_phase_req,
    .receiver_phase_ack,
    .receiver_phase_pending_q,
    .receiver_isolate_out,
    .receiver_clear_out
  );

endmodule


// ----------------------------------------------------------------------------
// Delay Model Helpers
// ----------------------------------------------------------------------------

// Per-bit inertial delay model used to sweep relative async channel timing in
// simulation without changing the production DUT hierarchy.
module cc_cdc_2phase_clearable_tb_bit_delay #(
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic in_i,
  output logic out_o
);

  timeunit 1ns;
  timeprecision 1ps;

  initial begin
    out_o = 1'b0;
  end

  always @(in_i) begin
    automatic int unsigned delay_ps;
    delay_ps = (MAX_DELAY_PS == 0) ? 0 : $urandom_range(0, MAX_DELAY_PS);
    out_o <= #(delay_ps * 1ps) in_i;
  end

endmodule


// Bus delay wrapper that applies independent random per-bit delay. This stresses
// bundled payload and phase buses under the same async timing assumptions.
module cc_cdc_2phase_clearable_tb_bus_delay #(
  parameter int unsigned Width = 1,
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  timeunit 1ns;
  timeprecision 1ps;

  for (genvar i = 0; i < Width; i++) begin : gen_bit_delay
    cc_cdc_2phase_clearable_tb_bit_delay #(
      .MAX_DELAY_PS ( MAX_DELAY_PS )
    ) i_delay (
      .in_i  ( in_i[i]  ),
      .out_o ( out_o[i] )
    );
  end

endmodule


// ----------------------------------------------------------------------------
// Timed Delay-Injection Harness
// ----------------------------------------------------------------------------

// Timed test harness equivalent to the clearable DUT, but with explicit delay
// elements inserted on all payload and reset-controller async wires.
module cc_cdc_2phase_clearable_tb_delay_injector
  import cc_pkg::*;
#(
  parameter int unsigned SYNC_STAGES = 3,
  parameter bit          CLEAR_ON_ASYNC_RESET = 1'b1,
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic        src_rst_ni,
  input  logic        src_clk_i,
  input  logic        src_clear_i,
  output logic        src_clear_pending_o,
  input  logic [31:0] src_data_i,
  input  logic        src_valid_i,
  output logic        src_ready_o,

  input  logic        dst_rst_ni,
  input  logic        dst_clk_i,
  input  logic        dst_clear_i,
  output logic        dst_clear_pending_o,
  output logic [31:0] dst_data_o,
  output logic        dst_valid_o,
  input  logic        dst_ready_i
);

  timeunit 1ns;
  timeprecision 1ps;

  localparam int unsigned ClearPhaseWidth = $bits(cdc_clear_seq_phase_e);

  logic        async_payload_req_from_src;
  logic        async_payload_req_to_dst;
  logic        async_payload_ack_from_dst;
  logic        async_payload_ack_to_src;
  logic [31:0] async_payload_data_from_src;
  logic [31:0] async_payload_data_to_dst;

  cdc_clear_seq_phase_e async_reset_src2dst_next_phase_from_src;
  cdc_clear_seq_phase_e async_reset_src2dst_next_phase_to_dst;
  cdc_clear_seq_phase_e async_reset_dst2src_next_phase_from_dst;
  cdc_clear_seq_phase_e async_reset_dst2src_next_phase_to_src;
  logic [ClearPhaseWidth-1:0] async_reset_src2dst_next_phase_from_src_bits;
  logic [ClearPhaseWidth-1:0] async_reset_src2dst_next_phase_to_dst_bits;
  logic [ClearPhaseWidth-1:0] async_reset_dst2src_next_phase_from_dst_bits;
  logic [ClearPhaseWidth-1:0] async_reset_dst2src_next_phase_to_src_bits;
  logic async_reset_src2dst_req_from_src;
  logic async_reset_src2dst_req_to_dst;
  logic async_reset_dst2src_ack_from_dst;
  logic async_reset_dst2src_ack_to_src;
  logic async_reset_dst2src_req_from_dst;
  logic async_reset_dst2src_req_to_src;
  logic async_reset_src2dst_ack_from_src;
  logic async_reset_src2dst_ack_to_dst;

  assign async_reset_src2dst_next_phase_from_src_bits = async_reset_src2dst_next_phase_from_src;
  assign async_reset_src2dst_next_phase_to_dst =
      cdc_clear_seq_phase_e'(async_reset_src2dst_next_phase_to_dst_bits);
  assign async_reset_dst2src_next_phase_from_dst_bits = async_reset_dst2src_next_phase_from_dst;
  assign async_reset_dst2src_next_phase_to_src =
      cdc_clear_seq_phase_e'(async_reset_dst2src_next_phase_to_src_bits);

  // Payload channel delays.
  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_payload_req_delay (
    .in_i  ( async_payload_req_from_src ),
    .out_o ( async_payload_req_to_dst   )
  );

  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_payload_ack_delay (
    .in_i  ( async_payload_ack_from_dst ),
    .out_o ( async_payload_ack_to_src   )
  );

  cc_cdc_2phase_clearable_tb_bus_delay #(
    .Width        ( 32           ),
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_payload_data_delay (
    .in_i  ( async_payload_data_from_src ),
    .out_o ( async_payload_data_to_dst   )
  );

  // Reset-controller phase, request, and acknowledge delays.
  cc_cdc_2phase_clearable_tb_bus_delay #(
    .Width        ( ClearPhaseWidth ),
    .MAX_DELAY_PS ( MAX_DELAY_PS    )
  ) i_async_reset_src2dst_next_phase_delay (
    .in_i  ( async_reset_src2dst_next_phase_from_src_bits ),
    .out_o ( async_reset_src2dst_next_phase_to_dst_bits   )
  );

  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_reset_src2dst_req_delay (
    .in_i  ( async_reset_src2dst_req_from_src ),
    .out_o ( async_reset_src2dst_req_to_dst   )
  );

  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_reset_dst2src_ack_delay (
    .in_i  ( async_reset_dst2src_ack_from_dst ),
    .out_o ( async_reset_dst2src_ack_to_src   )
  );

  cc_cdc_2phase_clearable_tb_bus_delay #(
    .Width        ( ClearPhaseWidth ),
    .MAX_DELAY_PS ( MAX_DELAY_PS    )
  ) i_async_reset_dst2src_next_phase_delay (
    .in_i  ( async_reset_dst2src_next_phase_from_dst_bits ),
    .out_o ( async_reset_dst2src_next_phase_to_src_bits   )
  );

  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_reset_dst2src_req_delay (
    .in_i  ( async_reset_dst2src_req_from_dst ),
    .out_o ( async_reset_dst2src_req_to_src   )
  );

  cc_cdc_2phase_clearable_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_reset_src2dst_ack_delay (
    .in_i  ( async_reset_src2dst_ack_from_src ),
    .out_o ( async_reset_src2dst_ack_to_dst   )
  );

  // Production domain wrappers connected through the delayed async wires.
  cc_cdc_2phase_src_domain_clearable #(
    .data_t            ( logic [31:0]        ),
    .SyncStages        ( SYNC_STAGES         ),
    .ClearOnAsyncReset ( CLEAR_ON_ASYNC_RESET )
  ) i_src_domain (
    .src_rst_ni,
    .src_clk_i,
    .src_clear_i,
    .src_clear_pending_o,
    .src_data_i,
    .src_valid_i,
    .src_ready_o,
    .async_payload_req_o       ( async_payload_req_from_src              ),
    .async_payload_ack_i       ( async_payload_ack_to_src                ),
    .async_payload_data_o      ( async_payload_data_from_src             ),
    .async_reset_next_phase_o  ( async_reset_src2dst_next_phase_from_src ),
    .async_reset_req_o         ( async_reset_src2dst_req_from_src        ),
    .async_reset_ack_i         ( async_reset_dst2src_ack_to_src          ),
    .async_reset_next_phase_i  ( async_reset_dst2src_next_phase_to_src   ),
    .async_reset_req_i         ( async_reset_dst2src_req_to_src          ),
    .async_reset_ack_o         ( async_reset_src2dst_ack_from_src        )
  );

  cc_cdc_2phase_dst_domain_clearable #(
    .data_t            ( logic [31:0]        ),
    .SyncStages        ( SYNC_STAGES         ),
    .ClearOnAsyncReset ( CLEAR_ON_ASYNC_RESET )
  ) i_dst_domain (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i,
    .dst_clear_pending_o,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,
    .async_payload_req_i       ( async_payload_req_to_dst                ),
    .async_payload_ack_o       ( async_payload_ack_from_dst              ),
    .async_payload_data_i      ( async_payload_data_to_dst               ),
    .async_reset_next_phase_o  ( async_reset_dst2src_next_phase_from_dst ),
    .async_reset_req_o         ( async_reset_dst2src_req_from_dst        ),
    .async_reset_ack_i         ( async_reset_src2dst_ack_to_dst          ),
    .async_reset_next_phase_i  ( async_reset_src2dst_next_phase_to_dst   ),
    .async_reset_req_i         ( async_reset_src2dst_req_to_dst          ),
    .async_reset_ack_o         ( async_reset_dst2src_ack_from_dst        )
  );
endmodule


// ----------------------------------------------------------------------------
// Reset-Controller Monitor
// ----------------------------------------------------------------------------

// Lightweight checker for reset-controller half internals. This is deliberately
// local-clock only and checks invariants that should hold after every edge.
module cc_cdc_reset_ctrlr_half_monitor
  import cc_pkg::*;
(
  input logic                 clk_i,
  input logic                 rst_ni,
  input logic                 isolate_o,
  input logic                 isolate_ack_i,
  input logic                 clear_o,
  input logic                 clear_ack_i,
  input cdc_clear_seq_phase_e async_next_phase_o,
  input logic                 async_req_o,
  input cdc_clear_seq_phase_e async_next_phase_i,
  input logic                 async_req_i,
  input logic [3:0]           initiator_state_q,
  input cdc_clear_seq_phase_e initiator_clear_seq_phase,
  input logic                 initiator_phase_transition_req,
  input logic                 initiator_isolate_out,
  input logic                 initiator_clear_out,
  input cdc_clear_seq_phase_e receiver_phase_q,
  input cdc_clear_seq_phase_e receiver_effective_phase,
  input cdc_clear_seq_phase_e receiver_next_phase,
  input logic                 receiver_phase_req,
  input logic                 receiver_phase_ack,
  input logic                 receiver_phase_pending_q,
  input logic                 receiver_isolate_out,
  input logic                 receiver_clear_out
);

  import cc_cdc_2phase_clearable_tb_monitor_pkg::report_monitor_error;

  timeunit 1ns;
  timeprecision 1ps;

  localparam logic [3:0] InitIdle                = 4'd0;
  localparam logic [3:0] InitIsolate             = 4'd1;
  localparam logic [3:0] InitWaitIsolatePhaseAck = 4'd2;
  localparam logic [3:0] InitWaitIsolateAck      = 4'd3;
  localparam logic [3:0] InitClear               = 4'd4;
  localparam logic [3:0] InitWaitClearPhaseAck   = 4'd5;
  localparam logic [3:0] InitWaitClearAck        = 4'd6;
  localparam logic [3:0] InitPostClear           = 4'd7;
  localparam logic [3:0] InitFinished            = 4'd8;

  // --------------------------------------------------------------------------
  // Monitor Helpers
  // --------------------------------------------------------------------------
  function automatic bit valid_phase(input cdc_clear_seq_phase_e phase);
    return phase inside {
      CDC_CLEAR_PHASE_IDLE,
      CDC_CLEAR_PHASE_ISOLATE,
      CDC_CLEAR_PHASE_CLEAR,
      CDC_CLEAR_PHASE_POST_CLEAR
    };
  endfunction

  function automatic bit valid_initiator_state(input logic [3:0] state);
    return state inside {
      InitIdle,
      InitIsolate,
      InitWaitIsolatePhaseAck,
      InitWaitIsolateAck,
      InitClear,
      InitWaitClearPhaseAck,
      InitWaitClearAck,
      InitPostClear,
      InitFinished
    };
  endfunction

  task automatic check_stable_outputs;
    if (clear_o && !isolate_o) begin
      report_monitor_error($sformatf("%m: clear_o asserted without isolate_o"));
    end

    if (initiator_clear_out && !initiator_isolate_out) begin
      report_monitor_error($sformatf("%m: initiator clear asserted without initiator isolate"));
    end

    if (receiver_clear_out && !receiver_isolate_out) begin
      report_monitor_error($sformatf("%m: receiver clear asserted without receiver isolate"));
    end

    if (clear_o !== (initiator_clear_out || receiver_clear_out)) begin
      report_monitor_error($sformatf("%m: clear_o does not match initiator/receiver clear outputs"));
    end

    if (isolate_o !== (initiator_isolate_out || receiver_isolate_out)) begin
      report_monitor_error(
          $sformatf("%m: isolate_o does not match initiator/receiver isolate outputs"));
    end

    if (async_req_o && !valid_phase(async_next_phase_o)) begin
      report_monitor_error($sformatf("%m: outgoing clear phase is illegal"));
    end

    if (initiator_phase_transition_req && !valid_phase(initiator_clear_seq_phase)) begin
      report_monitor_error($sformatf("%m: initiator requested an illegal clear phase"));
    end

    if (!valid_phase(receiver_effective_phase)) begin
      report_monitor_error($sformatf("%m: illegal effective receiver phase 0x%0h",
                                     receiver_effective_phase));
    end

    if (receiver_phase_req) begin
      if (!valid_phase(receiver_next_phase)) begin
        report_monitor_error($sformatf("%m: incoming receiver phase is illegal"));
      end
    end

    unique case (receiver_effective_phase)
      CDC_CLEAR_PHASE_IDLE: begin
        if (receiver_clear_out) begin
          report_monitor_error($sformatf("%m: receiver IDLE phase outputs are inconsistent"));
        end
      end
      CDC_CLEAR_PHASE_ISOLATE: begin
        if (receiver_clear_out || !receiver_isolate_out) begin
          report_monitor_error($sformatf("%m: receiver ISOLATE phase outputs are inconsistent"));
        end
      end
      CDC_CLEAR_PHASE_CLEAR: begin
        if (!receiver_clear_out || !receiver_isolate_out) begin
          report_monitor_error($sformatf("%m: receiver CLEAR phase outputs are inconsistent"));
        end
      end
      CDC_CLEAR_PHASE_POST_CLEAR: begin
        if (receiver_clear_out || !receiver_isolate_out) begin
          report_monitor_error(
              $sformatf("%m: receiver POST_CLEAR phase outputs are inconsistent"));
        end
      end
      default: begin
        if (receiver_clear_out || receiver_phase_ack) begin
          report_monitor_error(
              $sformatf("%m: receiver illegal phase was acknowledged or exposed"));
        end
      end
    endcase

    if (receiver_phase_ack && !receiver_phase_pending_q) begin
      report_monitor_error($sformatf("%m: receiver phase acknowledged before capture"));
    end

    if (receiver_phase_ack &&
        receiver_effective_phase == CDC_CLEAR_PHASE_CLEAR &&
        !clear_ack_i) begin
      report_monitor_error($sformatf("%m: receiver clear phase acknowledged before local ack"));
    end

    if (receiver_phase_ack &&
        receiver_effective_phase == CDC_CLEAR_PHASE_ISOLATE &&
        !isolate_ack_i) begin
      report_monitor_error($sformatf("%m: receiver isolate phase acknowledged before local ack"));
    end
  endtask

  // --------------------------------------------------------------------------
  // Edge Checks
  // --------------------------------------------------------------------------
  always @(posedge clk_i) begin
    if (rst_ni) begin
      #1ps;
      check_stable_outputs();

      if (!valid_initiator_state(initiator_state_q)) begin
        report_monitor_error($sformatf("%m: illegal initiator FSM state 0x%0h",
                                       initiator_state_q));
      end

      if (!valid_phase(receiver_phase_q)) begin
        report_monitor_error($sformatf("%m: illegal stored receiver phase 0x%0h",
                                       receiver_phase_q));
      end

      if (initiator_state_q inside {
            InitClear,
            InitWaitClearPhaseAck,
            InitWaitClearAck
          }) begin
        if (!initiator_clear_out || !initiator_isolate_out) begin
          report_monitor_error(
              $sformatf("%m: initiator clear state without clear/isolate outputs"));
        end
      end

      if (initiator_state_q inside {
            InitIsolate,
            InitWaitIsolatePhaseAck,
            InitWaitIsolateAck,
            InitPostClear,
            InitFinished
          }) begin
        if (!initiator_isolate_out || initiator_clear_out) begin
          report_monitor_error(
              $sformatf("%m: initiator isolate-only state has inconsistent outputs"));
        end
      end

      if (initiator_state_q == InitIdle) begin
        if (initiator_isolate_out || initiator_clear_out || initiator_phase_transition_req) begin
          report_monitor_error(
              $sformatf("%m: initiator IDLE state has active clear outputs or phase request"));
        end
      end
    end
  end

endmodule
