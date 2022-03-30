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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

module cdc_2phase_clearable_tb;

  parameter int UNTIL = 100000;
  parameter bit INJECT_DELAYS = 1;
  parameter int CLEAR_PPM = 2000;
  parameter int SYNC_STAGES = 3;


  time tck_src                = 10ns;
  time tck_dst                = 10ns;
  bit src_done                = 0;
  bit dst_done                = 0;
  bit done;
  assign done = src_done & dst_done;

  // Signals of the design under test.
  logic        src_rst_ni  = 1;
  logic        src_clk_i   = 0;
  logic [31:0] src_data_i  = 0;
  logic        src_clear_i = 0;
  logic        src_clear_pending_o;
  logic        src_valid_i = 0;
  logic        src_ready_o;

  logic        dst_rst_ni  = 1;
  logic        dst_clk_i   = 0;
  logic        dst_clear_i = 0;
  logic        dst_clear_pending_o;
  logic [31:0] dst_data_o;
  logic        dst_valid_o;
  logic        dst_ready_i = 0;

  // Instantiate the design under test.
  if (INJECT_DELAYS) begin : g_dut
    cdc_2phase_clearable_tb_delay_injector #(0.8ns) i_dut (.*);
  end else begin : g_dut
    cdc_2phase_clearable #(logic [31:0]) i_dut (.*);
  end

  typedef struct {
    int          data;
    bit          is_stale;
  } item_t;


  // Mailbox with expected items on destination side.
  item_t dst_mbox[$];
  int num_sent = 0;
  int num_received = 0;
  int num_failed = 0;

  // Clock generators.
  initial begin
    static int num_items, num_clks;
    num_items = 10;
    num_clks = 0;
    #10ns;
    src_rst_ni = 0;
    #10ns;
    src_rst_ni = 1;
    #10ns;
    while (!done) begin
      src_clk_i = 1;
      #(tck_src/2);
      src_clk_i = 0;
      #(tck_src/2);

      // Modulate the clock frequency.
      num_clks++;
      if (num_sent >= num_items && num_clks > 10) begin
        num_items = num_sent + 10;
        num_clks = 0;
        tck_src = $urandom_range(1000, 10000) * 1ps;
        assert(tck_src > 0);
      end
    end
  end

  initial begin
    static int num_items, num_clks;
    num_items = 10;
    num_clks = 0;
    #10ns;
    dst_rst_ni = 0;
    #10ns;
    dst_rst_ni = 1;
    #10ns;
    while (!done) begin
      dst_clk_i = 1;
      #(tck_dst/2);
      dst_clk_i = 0;
      #(tck_dst/2);

      // Modulate the clock frequency.
      num_clks++;
      if (num_received >= num_items && num_clks > 10) begin
        num_items = num_received + 10;
        num_clks = 0;
        tck_dst = $urandom_range(1000, 10000) * 1ps;
        assert(tck_dst > 0);
      end
    end
  end

  // Source side sender.
  task src_cycle_start;
    #(tck_src*0.8);
  endtask

  task src_cycle_end;
    @(posedge src_clk_i);
  endtask

  initial begin
    @(negedge src_rst_ni);
    @(posedge src_rst_ni);
    repeat(3) @(posedge src_clk_i);
    for (int i = 0; i < UNTIL; i++) begin
      static item_t stimulus;
      static bit     clear_cdc;
      stimulus.data  = $random();
      stimulus.is_stale = 1'b0;
      src_data_i    <= #(tck_src*0.2) stimulus.data;
      src_valid_i   <= #(tck_src*0.2) 1;
      dst_mbox.push_front(stimulus);
      num_sent++;
      src_cycle_start();
      while (!src_ready_o) begin
        src_cycle_end();
        src_cycle_start();
        // Ramdomly clear the CDC. During pending transaction
        clear_cdc = $urandom_range(0,1e6) < CLEAR_PPM;
        if (clear_cdc && !src_clear_pending_o) begin
          // The cdc shall be cleared. Mark all items in the mailbox as stale.
          foreach(dst_mbox[i]) begin
            if (!dst_mbox[i].is_stale) begin
              dst_mbox[i].is_stale = 1'b1;
              num_sent--;
            end
          end
          // Clear the CDC using either asynchronous or synchronous reset
          if ($urandom_range(0,1) == 1) begin
            $info("Randomly clearing CDC source-side synchronously");
            // Now raise the clear signal for one clock cycle.
            src_cycle_start();
            src_clear_i = 1'b1;
            src_valid_i = 1'b0;
            src_cycle_end();
            src_clear_i = #(tck_src*0.2) 1'b0;
          end else begin
            $info("Randomly resetting CDC source-side asynchronously");
            // Now assert the async reset signal for one clock cycle.
            src_cycle_start();
            src_rst_ni  = 1'b0;
            src_valid_i = 1'b0;
            src_cycle_end();
            src_rst_ni = #(tck_src*0.2) 1'b1;
          end
          break;
        end
      end
      src_cycle_end();
      src_valid_i <= #(tck_src*0.2) 0;
    end
    src_done = 1;
  end

  // Destination side receiver.
  task dst_cycle_start;
    #(tck_dst*0.8);
  endtask

  task dst_cycle_end;
    @(posedge dst_clk_i);
  endtask

  initial begin
    @(negedge dst_rst_ni);
    @(posedge dst_rst_ni);
    repeat(3) @(posedge dst_clk_i);
    while (!src_done || dst_mbox.size() > 0) begin
      static item_t expected;
      static integer actual;
      static int cooldown;
      static bit clear_cdc;
      //randomly drop the transaction by clearing from the destination side
      clear_cdc = $urandom_range(0,1e6) < CLEAR_PPM;
      if (clear_cdc && !dst_clear_pending_o) begin
        // Clear the CDC using either asynchronous or synchronous reset
        if ($urandom_range(0,1) == 1) begin
          $info("Randomly clearing CDC destination-side synchronously");
          // Now raise the clear signal for one clock cycle.
          dst_cycle_start();
          dst_clear_i = 1'b1;
          dst_ready_i = 1'b0;
          dst_cycle_end();
          dst_clear_i = #(tck_dst*0.2) 1'b0;
        end else begin
          $info("Randomly resetting CDC destination-side asynchronously");
          // Now assert the async reset signal for one clock cycle.
          dst_cycle_start();
          dst_rst_ni  = 1'b0;
          dst_ready_i = 1'b0;
          dst_cycle_end();
          dst_rst_ni = #(tck_dst*0.2) 1'b1;
        end
        // Wait for 1 dst clock cycle + SYNC_STAGES source clock cycles for the clear to propagate to the
        // other domain before clearing the mailbox (the pending item might be
        // consumsed by destination before the clear request arrives).
        @(posedge dst_clk_i);
        repeat(SYNC_STAGES) @(posedge src_clk_i);
        // and end the loop iteration at the rising edge of the dst clk
        dst_cycle_end();
        // Delete all pending items in the mailbox except for the last one
        while (dst_mbox.size() > 1) begin
          expected = dst_mbox.pop_back();
        end
      end else begin
        dst_ready_i <= #(tck_dst*0.2) 1;
        dst_cycle_start();
        while (!dst_valid_o) begin
          dst_cycle_end();
          dst_cycle_start();
        end
        actual = dst_data_o;
        num_received++;
        if (dst_mbox.size() == 0) begin
          $error("unexpected transaction: data=%0h", actual);
          num_failed++;
        end else begin
          expected = dst_mbox.pop_back();
          if (actual != expected.data) begin
            // Check if the expected item is a stale item. If so, pop all stale
            // items until we receive a fresh one and check again.
            while (dst_mbox.size() > 0  && expected.is_stale && expected.data != actual) begin
              expected = dst_mbox.pop_back();
            end
            if (actual != expected.data) begin
              $error("transaction mismatch: exp=%0h, act=%0h", expected.data, actual);
              num_failed++;
            end else begin
              if (!expected.is_stale) begin
                num_received++;
              end
            end
          end else if (expected.is_stale) begin
            $info("Received stale item after clear. This is expected to happen for some cycles after the clear until the clear propagated to the other side.");
          end else begin
            num_received++;
          end
        end
        dst_cycle_end();
        dst_ready_i <= #(tck_dst*0.2) 0;

        // Insert a random cooldown period.
        cooldown = $urandom_range(0, 40);
        if (cooldown < 20) repeat(cooldown) @(posedge dst_clk_i);
      end
    end

    if (num_failed > 0) begin
      $error("%0d/%0d items mismatched", num_failed, num_sent);
    end else begin
      $info("%0d items passed", num_sent);
    end

    dst_done = 1;
  end

endmodule


module cdc_2phase_clearable_tb_delay_injector #(
  parameter time MAX_DELAY = 0ns,
  parameter int SYNC_STAGES = 3
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

  logic async_req_o, async_req_i;
  logic async_ack_o, async_ack_i;
  logic [31:0] async_data_o, async_data_i;


  logic        s_src_clear;
  logic        s_src_ready;
  logic        s_dst_clear;
  logic        s_dst_valid;

  always @(async_req_o) begin
    automatic time d = $urandom_range(1ps, MAX_DELAY);
    async_req_i <= #d async_req_o;
  end

  always @(async_ack_o) begin
    automatic time d = $urandom_range(1ps, MAX_DELAY);
    async_ack_i <= #d async_ack_o;
  end

  for (genvar i = 0; i < 32; i++) begin
    always @(async_data_o[i]) begin
      automatic time d = $urandom_range(1ps, MAX_DELAY);
      async_data_i[i] <= #d async_data_o[i];
    end
  end

  cdc_2phase_src_clearable #(logic [31:0], SYNC_STAGES) i_src (
    .rst_ni       ( src_rst_ni                 ),
    .clk_i        ( src_clk_i                  ),
    .clear_i      ( s_src_clear                ),
    .data_i       ( src_data_i                 ),
    .valid_i      ( src_valid_i & !s_src_clear ),
    .ready_o      ( s_src_ready                ),
    .async_req_o  ( async_req_o                ),
    .async_ack_i  ( async_ack_i                ),
    .async_data_o ( async_data_o               )
  );

  assign src_ready_o = s_src_ready & !s_src_clear;

  cdc_2phase_dst_clearable #(logic [31:0], SYNC_STAGES) i_dst (
    .rst_ni       ( dst_rst_ni                 ),
    .clk_i        ( dst_clk_i                  ),
    .clear_i      ( s_dst_clear                ),
    .data_o       ( dst_data_o                 ),
    .valid_o      ( s_dst_valid                ),
    .ready_i      ( dst_ready_i & !s_dst_clear ),
    .async_req_i  ( async_req_i                ),
    .async_ack_o  ( async_ack_o                ),
    .async_data_i ( async_data_i               )
  );

  assign dst_valid_o = s_dst_valid & !s_dst_clear;

  // Synchronize the clear and reset signaling in both directions (see header of
  // the cdc_reset_ctrlr module for more details.)
  cdc_reset_ctrlr #(
    .SYNC_STAGES(SYNC_STAGES-1)
  ) i_cdc_reset_ctrlr (
    .a_clk_i   ( src_clk_i   ),
    .a_rst_ni  ( src_rst_ni  ),
    .a_clear_i ( src_clear_i ),
    .a_clear_o ( s_src_clear ),
    .b_clk_i   ( dst_clk_i   ),
    .b_rst_ni  ( dst_rst_ni  ),
    .b_clear_i ( dst_clear_i ),
    .b_clear_o ( s_dst_clear )
  );

  assign src_clear_pending_o = s_src_clear;
  assign dst_clear_pending_o = s_dst_clear;

endmodule
