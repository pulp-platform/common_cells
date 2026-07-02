// Copyright 2026 ETH Zurich and University of Bologna.
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
// - Philippe Sauter <phsauter@iis.ee.ethz.ch>
//
// Description: Gray-Counter CDC FIFO Testbench
// Exercise FIFO ordering, full/empty transitions, backpressure, gray pointer
// transitions, and timed async data/pointer delay sweeps for cc_cdc_fifo_gray.

module cc_cdc_fifo_gray_tb;

  timeunit 1ns;
  timeprecision 1ps;

  // --------------------------------------------------------------------------
  // Configuration
  // --------------------------------------------------------------------------
  parameter int unsigned NUM_RANDOM_TRANSFERS = 200;
  parameter int unsigned DEPTH = 3;
  parameter int unsigned SYNC_STAGES = 2;
  parameter int unsigned TCK_SRC_PS = 10000;
  parameter int unsigned TCK_DST_PS = 17000;
  parameter int unsigned TIMEOUT_CYCLES = 40000;
  parameter int unsigned SEED = 32'hf109_0001;
  parameter bit          INJECT_DELAYS = 1'b0;
  parameter int unsigned MAX_DELAY_PS = 0;
  parameter int unsigned SRC_START_DELAY_PS = 0;
  parameter int unsigned DST_START_DELAY_PS = 0;

  localparam int unsigned FifoDepth = 2**DEPTH;
  localparam int unsigned PtrWidth = DEPTH + 1;

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

  logic [PtrWidth-1:0] async_wptr_mon;
  logic [PtrWidth-1:0] async_rptr_mon;
  logic [PtrWidth-1:0] async_wptr_q = '0;
  logic [PtrWidth-1:0] async_rptr_q = '0;

  logic [31:0] expected_q[$];
  int unsigned num_src_handshakes = 0;
  int unsigned num_dst_handshakes = 0;
  int unsigned num_errors = 0;

  dst_ready_mode_e dst_ready_mode = DstReadyLow;

  // --------------------------------------------------------------------------
  // DUT Selection
  // --------------------------------------------------------------------------
  if (INJECT_DELAYS) begin : gen_delayed_dut
    cc_cdc_fifo_gray_tb_delay_injector #(
      .LOG_DEPTH    ( DEPTH        ),
      .SYNC_STAGES  ( SYNC_STAGES  ),
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
      .dst_ready_i,
      .async_wptr_mon_o ( async_wptr_mon ),
      .async_rptr_mon_o ( async_rptr_mon )
    );
  end else begin : gen_dut
    cc_cdc_fifo_gray #(
      .data_t     ( logic [31:0] ),
      .LogDepth   ( DEPTH        ),
      .SyncStages ( SYNC_STAGES  )
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

    assign async_wptr_mon = i_dut.async_wptr;
    assign async_rptr_mon = i_dut.async_rptr;
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
  // Gray Pointer Monitors
  // --------------------------------------------------------------------------
  always @(posedge src_clk_i) begin
    if (!src_rst_ni) begin
      async_wptr_q <= '0;
    end else begin
      check_gray_transition("async_wptr_o", async_wptr_q, async_wptr_mon);
      async_wptr_q <= async_wptr_mon;
    end
  end

  always @(posedge dst_clk_i) begin
    if (!dst_rst_ni) begin
      async_rptr_q <= '0;
    end else begin
      check_gray_transition("async_rptr_o", async_rptr_q, async_rptr_mon);
      async_rptr_q <= async_rptr_mon;
    end
  end

  // --------------------------------------------------------------------------
  // Test Helpers
  // --------------------------------------------------------------------------
  function automatic int unsigned count_set_bits(input logic [PtrWidth-1:0] value);
    int unsigned count;

    count = 0;
    for (int unsigned i = 0; i < PtrWidth; i++) begin
      if (value[i]) begin
        count++;
      end
    end
    return count;
  endfunction

  task automatic check_gray_transition(input string signal_name,
                                       input logic [PtrWidth-1:0] previous,
                                       input logic [PtrWidth-1:0] current);
    if (!$isunknown(previous) && !$isunknown(current) &&
        (count_set_bits(previous ^ current) > 1)) begin
      report_error($sformatf("%s changed more than one bit: previous=0x%0h current=0x%0h",
                             signal_name, previous, current));
    end
  endtask

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
    async_wptr_q = '0;
    async_rptr_q = '0;
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
      wait_src_cycles(8);
      wait_dst_cycles(8);
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

  task automatic wait_src_not_ready(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (!src_ready_o) begin
        return;
      end
      @(posedge src_clk_i or posedge dst_clk_i);
    end

    report_error($sformatf("timeout waiting for source not-ready in %s", test_name));
  endtask

  task automatic wait_dst_not_valid(input string test_name);
    for (int unsigned i = 0; i < TIMEOUT_CYCLES; i++) begin
      if (!dst_valid_o) begin
        return;
      end
      @(posedge dst_clk_i or posedge src_clk_i);
    end

    report_error($sformatf("timeout waiting for destination not-valid in %s", test_name));
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

  task automatic run_fill_drain_check(input string test_name, input logic [31:0] base);
    int unsigned max_fill_words;

    $display("%m: %s", test_name);
    max_fill_words = FifoDepth + 2;
    dst_ready_mode = DstReadyLow;
    wait_src_ready(test_name);
    for (int unsigned i = 0; i < max_fill_words; i++) begin
      send_word(base + i);
      if (!src_ready_o) begin
        break;
      end
    end
    wait_src_not_ready(test_name);
    dst_ready_mode = DstReadyHigh;
    wait_scoreboard_empty(test_name);
    wait_src_ready(test_name);
    wait_dst_not_valid(test_name);
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
    $display("%m: SEED=0x%08h derived=0x%08h DEPTH=%0d SYNC_STAGES=%0d",
             SEED, seed, DEPTH, SYNC_STAGES);

    reset_both_domains();

    run_transfer_check("basic fixed-ready transfer", FifoDepth + 8, 32'h1000_0000,
                       DstReadyHigh);
    run_fill_drain_check("fill and drain", 32'h2000_0000);
    run_transfer_check("randomized ready transfer", NUM_RANDOM_TRANSFERS, 32'h3000_0000,
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

module cc_cdc_fifo_gray_tb_bit_delay #(
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


module cc_cdc_fifo_gray_tb_bus_delay #(
  parameter int unsigned Width = 1,
  parameter int unsigned MAX_DELAY_PS = 0
)(
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  timeunit 1ns;
  timeprecision 1ps;

  for (genvar i = 0; i < Width; i++) begin : gen_bit_delay
    cc_cdc_fifo_gray_tb_bit_delay #(
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

module cc_cdc_fifo_gray_tb_delay_injector #(
  parameter int unsigned LOG_DEPTH = 3,
  parameter int unsigned SYNC_STAGES = 2,
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
  input  logic        dst_ready_i,

  output logic [LOG_DEPTH:0] async_wptr_mon_o,
  output logic [LOG_DEPTH:0] async_rptr_mon_o
);

  timeunit 1ns;
  timeprecision 1ps;

  localparam int unsigned PtrWidth = LOG_DEPTH + 1;
  typedef logic [31:0] data_t;

  data_t [2**LOG_DEPTH-1:0] async_data_from_src;
  data_t [2**LOG_DEPTH-1:0] async_data_to_dst;
  logic [PtrWidth-1:0] async_wptr_from_src;
  logic [PtrWidth-1:0] async_wptr_to_dst;
  logic [PtrWidth-1:0] async_rptr_from_dst;
  logic [PtrWidth-1:0] async_rptr_to_src;

  assign async_wptr_mon_o = async_wptr_from_src;
  assign async_rptr_mon_o = async_rptr_from_dst;

  cc_cdc_fifo_gray_src #(
    .data_t     ( data_t       ),
    .LogDepth   ( LOG_DEPTH    ),
    .SyncStages ( SYNC_STAGES  )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_data_i,
    .src_valid_i,
    .src_ready_o,
    .async_data_o ( async_data_from_src ),
    .async_wptr_o ( async_wptr_from_src ),
    .async_rptr_i ( async_rptr_to_src   )
  );

  for (genvar i = 0; i < 2**LOG_DEPTH; i++) begin : gen_data_delay
    cc_cdc_fifo_gray_tb_bus_delay #(
      .Width        ( 32           ),
      .MAX_DELAY_PS ( MAX_DELAY_PS )
    ) i_data_delay (
      .in_i  ( async_data_from_src[i] ),
      .out_o ( async_data_to_dst[i]   )
    );
  end

  cc_cdc_fifo_gray_tb_bus_delay #(
    .Width        ( PtrWidth     ),
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_wptr_delay (
    .in_i  ( async_wptr_from_src ),
    .out_o ( async_wptr_to_dst   )
  );

  cc_cdc_fifo_gray_tb_bus_delay #(
    .Width        ( PtrWidth     ),
    .MAX_DELAY_PS ( MAX_DELAY_PS )
  ) i_rptr_delay (
    .in_i  ( async_rptr_from_dst ),
    .out_o ( async_rptr_to_src   )
  );

  cc_cdc_fifo_gray_dst #(
    .data_t     ( data_t       ),
    .LogDepth   ( LOG_DEPTH    ),
    .SyncStages ( SYNC_STAGES  )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,
    .async_data_i ( async_data_to_dst   ),
    .async_wptr_i ( async_wptr_to_dst   ),
    .async_rptr_o ( async_rptr_from_dst )
  );

endmodule
