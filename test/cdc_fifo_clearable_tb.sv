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
// Manuel Eggimann <meggimann@iis.ee.ethz.ch>

module cdc_fifo_clearable_tb;

  parameter bit INJECT_SRC_STALLS = 0;
  parameter bit INJECT_DST_STALLS = 0;
  parameter int UNTIL = 100000;
  parameter int DEPTH = 3;
  parameter int CLEAR_PPM = 2000;

  time tck_src       = 10ns;
  time tck_dst       = 27ns;
  bit src_done       = 0;
  bit dst_done       = 0;
  bit done;
  assign done = src_done & dst_done;

  // Signals of the design under test.
  logic        src_rst_ni  = 1;
  logic        src_clk_i   = 0;
  logic        src_clear_i = 0;
  logic        src_clear_pending_o;
  logic [31:0] src_data_i  = 0;
  logic        src_valid_i = 0;
  logic        src_ready_o;

  logic        dst_rst_ni  = 1;
  logic        dst_clk_i   = 0;
  logic        dst_clear_i = 0;
  logic        dst_clear_pending_o;
  logic [31:0] dst_data_o;
  logic        dst_valid_o;
  logic        dst_ready_i = 0;

  assert property (@(posedge src_clk_i) !$isunknown(src_valid_i) && !$isunknown(src_ready_o));
  assert property (@(posedge dst_clk_i) !$isunknown(dst_valid_o) && !$isunknown(dst_ready_i));
  assert property (@(posedge src_clk_i) src_valid_i |-> !$isunknown(src_data_i));
  assert property (@(posedge dst_clk_i) dst_valid_o |-> !$isunknown(dst_data_o));

  // Instantiate the design under test.
  cdc_fifo_gray_clearable #(.T(logic [31:0]), .LOG_DEPTH(DEPTH)) i_dut (.*);

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
      item_t item;
      static integer stimulus;
      static int cooldown;
      static bit clear_cdc;
      // Ramdomly clear the CDC. When clearing the CDC, mark all remainig items
      // in the mailbox as stale. Some of them might still be received
      // downstream until the clear request propagated to the other side.
      clear_cdc    = $urandom_range(0,1e6) < CLEAR_PPM;
      if (!clear_cdc || src_clear_pending_o) begin
        stimulus       = $random();
        item.data      = stimulus;
        item.is_stale  = 1'b0;
        src_data_i    <= #(tck_src*0.2) stimulus;
        src_valid_i   <= #(tck_src*0.2) 1;
        num_sent++;
        src_cycle_start();
        while (!src_ready_o) begin
          src_cycle_end();
          src_cycle_start();
        end
        dst_mbox.push_front(item);
        src_cycle_end();
        src_valid_i <= #(tck_src*0.2) 0;

        // Insert a random cooldown period.
        if (INJECT_SRC_STALLS) begin
          cooldown = $urandom_range(0, 40);
          if (cooldown < 20) repeat(cooldown) @(posedge src_clk_i);
        end
      end else begin
        // The cdc shall be cleared. Mark all items in the mailbox as stale.
        foreach(dst_mbox[i]) begin
          if (!dst_mbox[i].is_stale) begin
            dst_mbox[i].is_stale = 1'b1;
            num_sent--;
          end
        end
        if ($urandom_range(0,1) == 1) begin
          $info("Randomly clearing CDC synchronously and marking all pending items as stale");
          // Now raise the clear signal for one clock cycle.
          src_cycle_start();
          src_clear_i = 1'b1;
          src_cycle_end();
          src_clear_i = #(tck_src*0.2) 1'b0;
        end else begin
          $info("Randomly resetting CDC asynchronously and marking all pending items as stale");
          // Now assert the async reset signal for one clock cycle.
          src_cycle_start();
          src_rst_ni = 1'b0;
          src_cycle_end();
          src_rst_ni = #(tck_src*0.2) 1'b1;
        end
      end
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
      static item_t expected_item;
      static integer actual;
      static int cooldown;
      static bit clear_cdc;
      // Ramdomly clear the CDC. When clearing the CDC, wait for exactly
      // DEPTH clock cycle for the clear request to propagate and then clear the
      // item queue.
      clear_cdc    = $urandom_range(0,1e6) < CLEAR_PPM;
      if (!clear_cdc || dst_clear_pending_o) begin
        dst_ready_i <= #(tck_dst*0.2) 1;
        dst_cycle_start();
        while (!dst_valid_o && !src_done) begin
          dst_cycle_end();
          dst_cycle_start();
        end
        if (src_done) break;
        actual = dst_data_o;
        if (dst_mbox.size() == 0) begin
          $error("unexpected transaction: data=%0h", actual);
          num_failed++;
        end else begin
          expected_item = dst_mbox.pop_back();
          if (actual != expected_item.data) begin
            // Check if the expected item is a stale item. If so, pop all stale
            // items until we receive a fresh one and check again.
            while (dst_mbox.size() > 0  && expected_item.is_stale && expected_item.data != actual) begin
              expected_item = dst_mbox.pop_back();
            end
            if (actual != expected_item.data) begin
              $error("transaction mismatch: exp=%0h, act=%0h", expected_item.data, actual);
              num_failed++;
            end else begin
              if (!expected_item.is_stale) begin
                num_received++;
              end
            end
          end else if (expected_item.is_stale) begin
            $info("Received stale item after clear. This is expected to happen for some cycles after the clear until the clear propagated to the other side.");
          end else begin
            num_received++;
          end
        end
        dst_cycle_end();
        dst_ready_i <= #(tck_dst*0.2) 0;

        // Insert a random cooldown period.
        if (INJECT_DST_STALLS) begin
          cooldown = $urandom_range(0, 40);
          if (cooldown < 20) repeat(cooldown) @(posedge dst_clk_i);
        end
      end else begin
        // Randomly alternate between async reset and synchronous clear
        if ($urandom_range(0,1) == 1) begin
          $info("Randomly clearing CDC synchronously from the destination side");
          dst_cycle_start();
          dst_clear_i = 1'b1;
          dst_cycle_end();
          dst_clear_i <= #(tck_dst*0.2) 1'b0;
        end else begin
          $info("Randomly resettting CDC asynchronously from the destination side");
          dst_cycle_start();
          dst_rst_ni = 1'b0;
          dst_cycle_end();
          dst_rst_ni <= #(tck_dst*0.2) 1'b1;
        end
        // Wait for exactly 1 dst clock cycle and DEPTH src clock cycles for the clear request to
        // propagate
        @(posedge dst_clk_i);
        repeat(DEPTH) @(posedge src_clk_i);
        // Now clear the item queue
        num_sent-=dst_mbox.size();
        dst_mbox.delete();

        // and end the loop iteration at the rising edge of the dst clk
        dst_cycle_end();
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
