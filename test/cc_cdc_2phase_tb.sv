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
// Description: Two-Phase CDC Testbench
// Exercise payload ordering, destination backpressure, and timed async-channel
// delay sweeps for cc_cdc_2phase.

module cc_cdc_2phase_tb;

  timeunit 1ns;
  timeprecision 1ps;

  // --------------------------------------------------------------------------
  // Configuration
  // --------------------------------------------------------------------------
  parameter int unsigned UNTIL = 0;
  parameter int unsigned NUM_RANDOM_TRANSFERS = 200;
  parameter int unsigned TCK_SRC_PS = 10000;
  parameter int unsigned TCK_DST_PS = 17000;
  parameter int unsigned TIMEOUT_CYCLES = 20000;
  parameter int unsigned SEED = 32'hcdc2_0001;
  parameter bit          INJECT_DELAYS = 1'b0;
  parameter int unsigned MAX_DELAY_PS = 0;
  parameter int unsigned SRC_START_DELAY_PS = 0;
  parameter int unsigned DST_START_DELAY_PS = 0;
  parameter bit          POST_SYNTHESIS = 1'b0;

  localparam int unsigned EffectiveRandomTransfers =
      (UNTIL == 0) ? NUM_RANDOM_TRANSFERS : UNTIL;

  typedef enum logic [1:0] {
    DstReadyLow,
    DstReadyHigh,
    DstReadyRandom
  } dst_ready_mode_e;

  time tck_src = TCK_SRC_PS * 1ps;
  time tck_dst = TCK_DST_PS * 1ps;

  logic        src_rst_ni = 1'b1;
  logic        src_clk_i = 1'b0;
  logic [31:0] src_data_i = '0;
  logic        src_valid_i = 1'b0;
  logic        src_ready_o;

  logic        dst_rst_ni = 1'b1;
  logic        dst_clk_i = 1'b0;
  logic [31:0] dst_data_o;
  logic        dst_valid_o;
  logic        dst_ready_i = 1'b0;

  logic [31:0] expected_q[$];
  int unsigned num_src_handshakes = 0;
  int unsigned num_dst_handshakes = 0;
  int unsigned num_errors = 0;

  dst_ready_mode_e dst_ready_mode = DstReadyLow;

  // --------------------------------------------------------------------------
  // DUT Selection
  // --------------------------------------------------------------------------
  // Instantiate either the plain DUT or the timed delay-injection harness used
  // by sweeps to perturb every explicit asynchronous channel.
  if (POST_SYNTHESIS) begin : gen_synth_dut
    cc_cdc_2phase_synth i_dut (
      .src_rst_ni,
      .src_clk_i,
      .src_data_i,
      .src_valid_i,
      .src_ready_o,
      .dst_rst_ni,
      .dst_clk_i,
      .dst_data_o,
      .dst_valid_o,
      .dst_ready_i
    );
  end else if (INJECT_DELAYS) begin : gen_delayed_dut
    cc_cdc_2phase_tb_delay_injector #(
      .MAX_DELAY_PS ( MAX_DELAY_PS )
    ) i_dut (
      .src_rst_ni,
      .src_clk_i,
      .src_data_i,
      .src_valid_i,
      .src_ready_o,
      .dst_rst_ni,
      .dst_clk_i,
      .dst_data_o,
      .dst_valid_o,
      .dst_ready_i
    );
  end else begin : gen_dut
    cc_cdc_2phase #(
      .data_t ( logic [31:0] )
    ) i_dut (
      .src_rst_ni,
      .src_clk_i,
      .src_data_i,
      .src_valid_i,
      .src_ready_o,
      .dst_rst_ni,
      .dst_clk_i,
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
  // Scoreboard source and destination handshakes.
  always @(posedge src_clk_i) begin
    if (src_rst_ni) begin
      if ($isunknown(src_ready_o)) begin
        report_error("src_ready_o is unknown");
      end
      if ($isunknown(src_valid_i)) begin
        report_error("src_valid_i is unknown");
      end
      if (src_valid_i && $isunknown(src_data_i)) begin
        report_error("src_data_i is unknown while valid");
      end
      if (src_valid_i && src_ready_o) begin
        num_src_handshakes++;
        expected_q.push_back(src_data_i);
      end
    end
  end

  always @(posedge dst_clk_i) begin
    logic [31:0] expected;

    if (dst_rst_ni) begin
      if ($isunknown(dst_valid_o)) begin
        report_error("dst_valid_o is unknown");
      end
      if ($isunknown(dst_ready_i)) begin
        report_error("dst_ready_i is unknown");
      end
      if (dst_valid_o && $isunknown(dst_data_o)) begin
        report_error("dst_data_o is unknown while valid");
      end
      if (dst_valid_o && dst_ready_i) begin
        num_dst_handshakes++;
        if (expected_q.size() == 0) begin
          report_error($sformatf("unexpected destination transaction: data=0x%08h",
                                 dst_data_o));
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
  task automatic report_error(input string msg);
    num_errors++;
    $error("%s", msg);
  endtask

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

  task automatic reset_both_domains;
    expected_q.delete();
    src_data_i = '0;
    src_valid_i = 1'b0;
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
  endtask

  task automatic send_word(input logic [31:0] data);
    @(negedge src_clk_i);
    #1ps;
    src_data_i = data;
    src_valid_i = 1'b1;

    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (src_ready_o) begin
        @(posedge src_clk_i);
        @(negedge src_clk_i);
        src_valid_i = 1'b0;
        src_data_i = '0;
        return;
      end
      @(negedge src_clk_i);
    end

    report_error($sformatf("timeout sending data=0x%08h", data));
    src_valid_i = 1'b0;
  endtask

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

  task automatic run_backpressure_check(input string test_name, input logic [31:0] data,
                                        input logic [31:0] post_base);
    $display("%m: %s", test_name);
    dst_ready_mode = DstReadyLow;
    wait_src_ready(test_name);
    send_word(data);
    wait_dst_valid(test_name);
    wait_dst_cycles($urandom_range(4, 12));
    dst_ready_mode = DstReadyHigh;
    wait_scoreboard_empty(test_name);
    wait_src_ready(test_name);
    run_transfer_check({test_name, " recovery transfer"}, 8, post_base, DstReadyHigh);
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

    run_transfer_check("basic fixed-ready transfer", 32, 32'h1000_0000, DstReadyHigh);
    run_backpressure_check("destination backpressure", 32'h2000_0001, 32'h2000_1000);
    run_transfer_check("randomized ready transfer", EffectiveRandomTransfers, 32'h3000_0000,
                       DstReadyRandom);

    if ((num_errors != 0) || (expected_q.size() != 0)) begin
      $fatal(1, "%m: failed with %0d errors and %0d pending scoreboard items",
             num_errors, expected_q.size());
    end

    $display("%m: passed: src_handshakes=%0d dst_handshakes=%0d",
             num_src_handshakes, num_dst_handshakes);
    $finish;
  end

endmodule


// ----------------------------------------------------------------------------
// Delay Model Helpers
// ----------------------------------------------------------------------------

// Per-bit inertial delay model used to sweep relative async channel timing in
// simulation without changing the production DUT hierarchy.
module cc_cdc_2phase_tb_bit_delay #(
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
// bundled payload under the same async timing assumptions as the control wires.
module cc_cdc_2phase_tb_bus_delay #(
  parameter int unsigned Width = 1,
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  timeunit 1ns;
  timeprecision 1ps;

  for (genvar i = 0; i < Width; i++) begin : gen_bit_delay
    cc_cdc_2phase_tb_bit_delay #(
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

// Timed test harness equivalent to the DUT, but with explicit delay elements
// inserted on all payload async wires.
module cc_cdc_2phase_tb_delay_injector #(
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic        src_rst_ni,
  input  logic        src_clk_i,
  input  logic [31:0] src_data_i,
  input  logic        src_valid_i,
  output logic        src_ready_o,

  input  logic        dst_rst_ni,
  input  logic        dst_clk_i,
  output logic [31:0] dst_data_o,
  output logic        dst_valid_o,
  input  logic        dst_ready_i
);

  timeunit 1ns;
  timeprecision 1ps;

  logic        async_req_from_src;
  logic        async_req_to_dst;
  logic        async_ack_from_dst;
  logic        async_ack_to_src;
  logic [31:0] async_data_from_src;
  logic [31:0] async_data_to_dst;

  cc_cdc_2phase_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_req_delay (
    .in_i  ( async_req_from_src ),
    .out_o ( async_req_to_dst   )
  );

  cc_cdc_2phase_tb_bit_delay #(
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_ack_delay (
    .in_i  ( async_ack_from_dst ),
    .out_o ( async_ack_to_src   )
  );

  cc_cdc_2phase_tb_bus_delay #(
    .Width        ( 32           ),
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_async_data_delay (
    .in_i  ( async_data_from_src ),
    .out_o ( async_data_to_dst   )
  );

  cc_cdc_2phase_src #(
    .data_t ( logic [31:0] )
  ) i_src (
    .rst_ni       ( src_rst_ni          ),
    .clk_i        ( src_clk_i           ),
    .data_i       ( src_data_i          ),
    .valid_i      ( src_valid_i         ),
    .ready_o      ( src_ready_o         ),
    .async_req_o  ( async_req_from_src  ),
    .async_ack_i  ( async_ack_to_src    ),
    .async_data_o ( async_data_from_src )
  );

  cc_cdc_2phase_dst #(
    .data_t ( logic [31:0] )
  ) i_dst (
    .rst_ni       ( dst_rst_ni        ),
    .clk_i        ( dst_clk_i         ),
    .data_o       ( dst_data_o        ),
    .valid_o      ( dst_valid_o       ),
    .ready_i      ( dst_ready_i       ),
    .async_req_i  ( async_req_to_dst  ),
    .async_ack_o  ( async_ack_from_dst ),
    .async_data_i ( async_data_to_dst )
  );

endmodule
