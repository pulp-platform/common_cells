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
// Description: Composed Reset-Controller Properties
// Instantiate the bidirectional reset controller with a one-cycle local
// acknowledgement model and prove cross-domain clear/isolate sequencing.

module cc_cdc_reset_ctrlr_composed_harness (
  input wire a_clk_i,
  input wire a_rst_ni,
  input wire a_clear_i,
  input wire b_clk_i,
  input wire b_rst_ni,
  input wire b_clear_i
);

  logic a_clear_o;
  logic a_clear_ack_q;
  logic a_isolate_o;
  logic a_isolate_ack_q;
  logic b_clear_o;
  logic b_clear_ack_q;
  logic b_isolate_o;
  logic b_isolate_ack_q;

  logic a_init_q = 1'b0;
  logic b_init_q = 1'b0;

  localparam int unsigned ResetCtrlrSyncStages = 2;
  localparam int unsigned MaxRelativeClockCycles = 16;
  localparam int unsigned ProgressBoundCycles =
      MaxRelativeClockCycles * (20 + 16 * ResetCtrlrSyncStages + 4);
  localparam int unsigned ProgressCounterWidth = $clog2(ProgressBoundCycles + 1);
  localparam int unsigned ClockGapCounterWidth = $clog2(MaxRelativeClockCycles + 1);

  logic clear_sequence_idle;
  logic a_clock_beat_q;
  logic b_clock_beat_q;
  logic a_seen_b_clock_beat_q;
  logic b_seen_a_clock_beat_q;
  logic [ClockGapCounterWidth-1:0] a_cycles_without_b_clock_q;
  logic [ClockGapCounterWidth-1:0] b_cycles_without_a_clock_q;
  logic a_progress_armed_q;
  logic a_progress_active_q;
  logic a_progress_seen_clear_q;
  logic [ProgressCounterWidth-1:0] a_progress_cycles_q;
  logic b_progress_armed_q;
  logic b_progress_active_q;
  logic b_progress_seen_clear_q;
  logic [ProgressCounterWidth-1:0] b_progress_cycles_q;

  assign clear_sequence_idle = !(a_isolate_o || a_clear_o || b_isolate_o || b_clear_o);

  // Composed harness: instantiate both halves through the public controller and
  // model a CDC user that acknowledges isolate/clear one local cycle later.
  cc_cdc_reset_ctrlr #(
    .SyncStages        ( 2    ),
    .ClearOnAsyncReset ( 1'b1 )
  ) i_dut (
    .a_clk_i,
    .a_rst_ni,
    .a_clear_i,
    .a_clear_o,
    .a_clear_ack_i   ( a_clear_ack_q   ),
    .a_isolate_o,
    .a_isolate_ack_i ( a_isolate_ack_q ),
    .b_clk_i,
    .b_rst_ni,
    .b_clear_i,
    .b_clear_o,
    .b_clear_ack_i   ( b_clear_ack_q   ),
    .b_isolate_o,
    .b_isolate_ack_i ( b_isolate_ack_q )
  );

  always_ff @(posedge a_clk_i) begin
    a_init_q <= 1'b1;
    if (!a_init_q) begin
      assume (!a_rst_ni);
    end
  end

  always_ff @(posedge b_clk_i) begin
    b_init_q <= 1'b1;
    if (!b_init_q) begin
      assume (!b_rst_ni);
    end
  end

  always_comb begin
    if (a_init_q) begin
      assume (a_rst_ni);
    end else begin
      assume (!a_clear_i);
    end

    if (b_init_q) begin
      assume (b_rst_ni);
    end else begin
      assume (!b_clear_i);
    end
  end

  always_ff @(posedge a_clk_i, negedge a_rst_ni) begin
    if (!a_rst_ni) begin
      a_isolate_ack_q <= 1'b0;
      a_clear_ack_q   <= 1'b0;
    end else begin
      a_isolate_ack_q <= a_isolate_o;
      a_clear_ack_q   <= a_clear_o;
    end
  end

  always_ff @(posedge b_clk_i, negedge b_rst_ni) begin
    if (!b_rst_ni) begin
      b_isolate_ack_q <= 1'b0;
      b_clear_ack_q   <= 1'b0;
    end else begin
      b_isolate_ack_q <= b_isolate_o;
      b_clear_ack_q   <= b_clear_o;
    end
  end

  always_comb begin
    if (a_rst_ni) begin
      assert (!a_clear_o || a_isolate_o);
    end

    if (b_rst_ni) begin
      assert (!b_clear_o || b_isolate_o);
    end

    if (a_rst_ni && b_rst_ni) begin
      assert (!(a_clear_o || b_clear_o) || (a_isolate_o && b_isolate_o));
    end
  end

  // Side-A sequential checks validate the one-cycle acknowledgement model and
  // cover a sequence initiated from A that propagates isolation to B. The
  // clock-beat assumption bounds relative clock stalls so the progress watchdog
  // can turn clear-sequence deadlocks into bounded safety checks.
  always_ff @(posedge a_clk_i) begin
    if (!a_rst_ni) begin
      a_clock_beat_q <= 1'b0;
    end else begin
      a_clock_beat_q <= ~a_clock_beat_q;
    end

    if (a_rst_ni && $past(a_rst_ni) && a_init_q) begin
      assert (a_isolate_ack_q == $past(a_isolate_o));
      assert (a_clear_ack_q == $past(a_clear_o));
    end

    if (!a_rst_ni || !b_rst_ni || !a_init_q || !b_init_q) begin
      a_seen_b_clock_beat_q       <= b_clock_beat_q;
      a_cycles_without_b_clock_q  <= '0;
    end else if (a_seen_b_clock_beat_q != b_clock_beat_q) begin
      a_seen_b_clock_beat_q       <= b_clock_beat_q;
      a_cycles_without_b_clock_q  <= '0;
    end else begin
      a_cycles_without_b_clock_q <= a_cycles_without_b_clock_q + 1'b1;
      assume (a_cycles_without_b_clock_q < MaxRelativeClockCycles);
    end

    if (a_rst_ni && b_rst_ni && $past(a_rst_ni) && $past(b_rst_ni) &&
        a_init_q && b_init_q && $past(a_init_q) && $past(b_init_q) &&
        $past(a_clear_i)) begin
      assert (a_isolate_o);
    end

    if (!a_rst_ni || !b_rst_ni || !a_init_q || !b_init_q) begin
      a_progress_armed_q      <= 1'b0;
      a_progress_active_q     <= 1'b0;
      a_progress_seen_clear_q <= 1'b0;
      a_progress_cycles_q     <= '0;
    end else if (!a_progress_armed_q) begin
      a_progress_armed_q      <= clear_sequence_idle;
      a_progress_active_q     <= 1'b0;
      a_progress_seen_clear_q <= 1'b0;
      a_progress_cycles_q     <= '0;
    end else if (clear_sequence_idle) begin
      if (a_progress_active_q) begin
        assert (a_progress_seen_clear_q);
      end
      a_progress_active_q     <= 1'b0;
      a_progress_seen_clear_q <= 1'b0;
      a_progress_cycles_q     <= '0;
    end else begin
      a_progress_active_q     <= 1'b1;
      a_progress_seen_clear_q <= a_progress_seen_clear_q || a_clear_o;
      a_progress_cycles_q     <= a_progress_cycles_q + 1'b1;
      assert (a_progress_cycles_q < ProgressBoundCycles);
    end

    cover (a_rst_ni && b_rst_ni && a_clear_o && b_isolate_o);
  end

  // Side-B sequential checks mirror the side-A properties and cover a sequence
  // initiated from B that propagates isolation to A.
  always_ff @(posedge b_clk_i) begin
    if (!b_rst_ni) begin
      b_clock_beat_q <= 1'b0;
    end else begin
      b_clock_beat_q <= ~b_clock_beat_q;
    end

    if (b_rst_ni && $past(b_rst_ni) && b_init_q) begin
      assert (b_isolate_ack_q == $past(b_isolate_o));
      assert (b_clear_ack_q == $past(b_clear_o));
    end

    if (!a_rst_ni || !b_rst_ni || !a_init_q || !b_init_q) begin
      b_seen_a_clock_beat_q       <= a_clock_beat_q;
      b_cycles_without_a_clock_q  <= '0;
    end else if (b_seen_a_clock_beat_q != a_clock_beat_q) begin
      b_seen_a_clock_beat_q       <= a_clock_beat_q;
      b_cycles_without_a_clock_q  <= '0;
    end else begin
      b_cycles_without_a_clock_q <= b_cycles_without_a_clock_q + 1'b1;
      assume (b_cycles_without_a_clock_q < MaxRelativeClockCycles);
    end

    if (a_rst_ni && b_rst_ni && $past(a_rst_ni) && $past(b_rst_ni) &&
        a_init_q && b_init_q && $past(a_init_q) && $past(b_init_q) &&
        $past(b_clear_i)) begin
      assert (b_isolate_o);
    end

    if (!a_rst_ni || !b_rst_ni || !a_init_q || !b_init_q) begin
      b_progress_armed_q      <= 1'b0;
      b_progress_active_q     <= 1'b0;
      b_progress_seen_clear_q <= 1'b0;
      b_progress_cycles_q     <= '0;
    end else if (!b_progress_armed_q) begin
      b_progress_armed_q      <= clear_sequence_idle;
      b_progress_active_q     <= 1'b0;
      b_progress_seen_clear_q <= 1'b0;
      b_progress_cycles_q     <= '0;
    end else if (clear_sequence_idle) begin
      if (b_progress_active_q) begin
        assert (b_progress_seen_clear_q);
      end
      b_progress_active_q     <= 1'b0;
      b_progress_seen_clear_q <= 1'b0;
      b_progress_cycles_q     <= '0;
    end else begin
      b_progress_active_q     <= 1'b1;
      b_progress_seen_clear_q <= b_progress_seen_clear_q || b_clear_o;
      b_progress_cycles_q     <= b_progress_cycles_q + 1'b1;
      assert (b_progress_cycles_q < ProgressBoundCycles);
    end

    cover (a_rst_ni && b_rst_ni && b_clear_o && a_isolate_o);
  end

endmodule
