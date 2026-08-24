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
// Instantiate the bidirectional reset controller with unconstrained, legal
// acknowledgement inputs and check the causal clear/isolate protocol.

// verilog_lint: waive module-filename
module cc_cdc_reset_ctrlr_composed_harness (
  input wire a_clk_i,
  input wire a_rst_ni,
  input wire a_clear_i,
  input wire a_clear_ack_i,
  input wire a_isolate_ack_i,
  input wire b_clk_i,
  input wire b_rst_ni,
  input wire b_clear_i,
  input wire b_clear_ack_i,
  input wire b_isolate_ack_i
);

  logic a_clear_o;
  logic a_isolate_o;
  logic b_clear_o;
  logic b_isolate_o;

  logic a_init_q = 1'b0;
  logic b_init_q = 1'b0;

  // A monitor epoch is deliberately local to the sampled clock.  CANCELED is
  // entered during the sampled initial reset, so the initial reset epoch does
  // not inherit ordering obligations from an uninitialized state.
  typedef enum logic [2:0] {
    ObserveCanceled,
    ObserveIdle,
    ObserveIsolate,
    ObserveClear,
    ObservePostClear
  } observe_phase_e;

  observe_phase_e a_observe_phase_q;
  observe_phase_e b_observe_phase_q;

  logic clear_sequence_idle;
  logic a_idle_capture_only;
  logic b_idle_capture_only;

  // Cover-state encoding tracks every externally visible protocol phase,
  // including the final return to idle.
  localparam logic [2:0] CoverIdle       = 3'd0;
  localparam logic [2:0] CoverIsolate    = 3'd1;
  localparam logic [2:0] CoverClear      = 3'd2;
  localparam logic [2:0] CoverPostClear  = 3'd3;
  localparam logic [2:0] CoverReturnIdle = 3'd4;
  localparam logic [2:0] CoverDone       = 3'd5;

  logic [2:0] cover_a_origin_q          = CoverIdle;
  logic [2:0] cover_b_origin_q          = CoverIdle;
  logic [2:0] cover_simultaneous_origin_q = CoverIdle;
  logic       cover_ready_q             = 1'b0;

  assign clear_sequence_idle = !(a_isolate_o || a_clear_o ||
                                 b_isolate_o || b_clear_o);
  // Capturing the final IDLE phase deliberately raises receiver isolation for
  // one cycle.  It is an ordering margin, not the start of another clear
  // epoch, unless the local initiator is independently isolating.
  assign a_idle_capture_only =
      i_dut.i_cdc_reset_ctrlr_half_a.receiver_capture_phase &&
      (i_dut.i_cdc_reset_ctrlr_half_a.receiver_next_phase == 2'd0) &&
      !i_dut.i_cdc_reset_ctrlr_half_a.initiator_isolate_out;
  assign b_idle_capture_only =
      i_dut.i_cdc_reset_ctrlr_half_b.receiver_capture_phase &&
      (i_dut.i_cdc_reset_ctrlr_half_b.receiver_next_phase == 2'd0) &&
      !i_dut.i_cdc_reset_ctrlr_half_b.initiator_isolate_out;

  // Composed harness: instantiate both halves through the public controller.
  // The acknowledgement inputs below are unconstrained by the harness.  The
  // environment allows arbitrary completion latency, level-sticky
  // acknowledgement while a request is active, and one sampled trailing-high
  // cycle after withdrawal; no eventual acknowledgement is assumed.
  cc_cdc_reset_ctrlr #(
    .SyncStages        ( 2    ),
    .ClearOnAsyncReset ( 1'b1 )
  ) i_dut (
    .a_clk_i,
    .a_rst_ni,
    .a_clear_i,
    .a_clear_o,
    .a_clear_ack_i,
    .a_isolate_o,
    .a_isolate_ack_i,
    .b_clk_i,
    .b_rst_ni,
    .b_clear_i,
    .b_clear_o,
    .b_clear_ack_i,
    .b_isolate_o,
    .b_isolate_ack_i
  );

  // Sample reset assertion independently in each clock domain.  The formal
  // model then keeps each reset released; later asynchronous reset assertion
  // and reset-during-transaction behavior are outside this follow-up proof.
  always_ff @(posedge a_clk_i) begin
    a_init_q <= 1'b1;
    if (!a_init_q) begin
      assume (!a_rst_ni);
    end

    // External completion levels may assert at any latency.  Once an
    // acknowledgement is high during an active request it remains high while
    // that request is active, with at most one sampled trailing-high cycle
    // after withdrawal.  A high acknowledgement from a prior request cannot
    // leak into a later request epoch.
    if (a_init_q && a_rst_ni && $past(a_rst_ni)) begin
      if (a_clear_ack_i)
        assume (a_clear_o || ($past(a_clear_o) && $past(a_clear_ack_i)));
      if (a_isolate_ack_i)
        assume (a_isolate_o || ($past(a_isolate_o) && $past(a_isolate_ack_i)));

      if ($past(a_clear_ack_i && a_clear_o) && a_clear_o)
        assume (a_clear_ack_i);
      if ($past(a_isolate_ack_i && a_isolate_o) && a_isolate_o)
        assume (a_isolate_ack_i);

      if (a_clear_o && !$past(a_clear_o) && $past(a_clear_ack_i))
        assume (!a_clear_ack_i);
      if (a_isolate_o && !$past(a_isolate_o) && $past(a_isolate_ack_i))
        assume (!a_isolate_ack_i);
    end else if (a_init_q && a_rst_ni && !$past(a_rst_ni)) begin
      // Do not carry an acknowledgement from the sampled reset epoch into
      // the first active request.
      if (a_clear_ack_i)
        assume (a_clear_o);
      if (a_isolate_ack_i)
        assume (a_isolate_o);
    end

  end

  always_ff @(posedge b_clk_i) begin
    b_init_q <= 1'b1;
    if (!b_init_q) begin
      assume (!b_rst_ni);
    end

    // Symmetric acknowledgement epoch contract for side B.
    if (b_init_q && b_rst_ni && $past(b_rst_ni)) begin
      if (b_clear_ack_i)
        assume (b_clear_o || ($past(b_clear_o) && $past(b_clear_ack_i)));
      if (b_isolate_ack_i)
        assume (b_isolate_o || ($past(b_isolate_o) && $past(b_isolate_ack_i)));

      if ($past(b_clear_ack_i && b_clear_o) && b_clear_o)
        assume (b_clear_ack_i);
      if ($past(b_isolate_ack_i && b_isolate_o) && b_isolate_o)
        assume (b_isolate_ack_i);

      if (b_clear_o && !$past(b_clear_o) && $past(b_clear_ack_i))
        assume (!b_clear_ack_i);
      if (b_isolate_o && !$past(b_isolate_o) && $past(b_isolate_ack_i))
        assume (!b_isolate_ack_i);
    end else if (b_init_q && b_rst_ni && !$past(b_rst_ni)) begin
      if (b_clear_ack_i)
        assume (b_clear_o);
      if (b_isolate_ack_i)
        assume (b_isolate_o);
    end

  end

  // Once each domain has sampled its initial reset, keep that reset released
  // for the remainder of this synchronous-clear proof.  This excludes later
  // asynchronous assertions and reset-during-transaction behavior.
  always_comb begin
    if (a_init_q) begin
      assume (a_rst_ni);
    end
    if (b_init_q) begin
      assume (b_rst_ni);
    end
  end

  // The safety acknowledgement epochs are constrained in the clocked blocks
  // above.  The cover task specializes them to zero-added-latency completion
  // levels to avoid redundant delay choices while demonstrating complete
  // phase sequences.
  always_comb begin
`ifdef CC_CDC_RESET_CTRLR_COVER
    assume (a_clear_ack_i == a_clear_o);
    assume (a_isolate_ack_i == a_isolate_o);
    assume (b_clear_ack_i == b_clear_o);
    assume (b_isolate_ack_i == b_isolate_o);
`endif
  end

  // Cross-domain safety contract.  The first two assertions are local
  // obligations; the third prevents either side from clearing while the other
  // side is not isolated.  During reset the interface is being canceled, so
  // cross-domain assertions are enabled only once both resets are released.
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

  // Causal monitor for side A.  Every non-canceled epoch must be observed as
  // isolate -> clear -> post-clear -> idle.  The sampled initial reset
  // cancels both local observations before synchronous clear epochs begin.
  always_ff @(posedge a_clk_i) begin
    if (!a_init_q || !b_init_q) begin
      a_observe_phase_q <= ObserveCanceled;
    end else begin
      case (a_observe_phase_q)
        ObserveCanceled: begin
          if (a_clear_o) begin
            // A canceled epoch may be observed first at CLEAR after reset; it
            // must nevertheless retain the local isolation invariant.
            assert (a_isolate_o);
            a_observe_phase_q <= ObserveClear;
          end else if (a_isolate_o && !a_idle_capture_only) begin
            a_observe_phase_q <= ObserveIsolate;
          end else begin
            a_observe_phase_q <= ObserveIdle;
          end
        end

        ObserveIdle: begin
          assert (!a_clear_o);
          if (a_isolate_o && !a_idle_capture_only) begin
            a_observe_phase_q <= ObserveIsolate;
          end
        end

        ObserveIsolate: begin
          assert (a_isolate_o);
          if (a_clear_o) begin
            a_observe_phase_q <= ObserveClear;
          end else if (!a_isolate_o) begin
            // Isolation cannot return to idle before this epoch has observed
            // both clear and post-clear.
            assert (1'b0);
            a_observe_phase_q <= ObserveIdle;
          end
        end

        ObserveClear: begin
          assert (a_isolate_o);
          if (!a_clear_o) begin
            // Leaving CLEAR is the observation of POST_CLEAR, so isolation
            // must still be active on this sample.
            assert (a_isolate_o);
            a_observe_phase_q <= ObservePostClear;
          end
        end

        ObservePostClear: begin
          // Concurrent local and remote requests can start another clear pulse
          // before their combined isolation interval ends.  Treat that as a
          // new CLEAR phase within the same isolated epoch.
          if (a_clear_o) begin
            a_observe_phase_q <= ObserveClear;
          end else if (!a_isolate_o) begin
            a_observe_phase_q <= ObserveIdle;
          end
        end

        default: begin
          a_observe_phase_q <= ObserveCanceled;
        end
      endcase
    end
  end

  // Causal monitor for side B, symmetric to side A.
  always_ff @(posedge b_clk_i) begin
    if (!a_init_q || !b_init_q) begin
      b_observe_phase_q <= ObserveCanceled;
    end else begin
      case (b_observe_phase_q)
        ObserveCanceled: begin
          if (b_clear_o) begin
            assert (b_isolate_o);
            b_observe_phase_q <= ObserveClear;
          end else if (b_isolate_o && !b_idle_capture_only) begin
            b_observe_phase_q <= ObserveIsolate;
          end else begin
            b_observe_phase_q <= ObserveIdle;
          end
        end

        ObserveIdle: begin
          assert (!b_clear_o);
          if (b_isolate_o && !b_idle_capture_only) begin
            b_observe_phase_q <= ObserveIsolate;
          end
        end

        ObserveIsolate: begin
          assert (b_isolate_o);
          if (b_clear_o) begin
            b_observe_phase_q <= ObserveClear;
          end else if (!b_isolate_o) begin
            assert (1'b0);
            b_observe_phase_q <= ObserveIdle;
          end
        end

        ObserveClear: begin
          assert (b_isolate_o);
          if (!b_clear_o) begin
            assert (b_isolate_o);
            b_observe_phase_q <= ObservePostClear;
          end
        end

        ObservePostClear: begin
          if (b_clear_o) begin
            b_observe_phase_q <= ObserveClear;
          end else if (!b_isolate_o) begin
            b_observe_phase_q <= ObserveIdle;
          end
        end

        default: begin
          b_observe_phase_q <= ObserveCanceled;
        end
      endcase
    end
  end

  // Bounded cover monitor.  The three origin cases exercise A-only, B-only,
  // and simultaneous clear requests.  Each case requires the complete
  // ordered output sequence after the sampled initial reset recovery.
  always_ff @(posedge a_clk_i) begin
    if (a_rst_ni && b_rst_ni && clear_sequence_idle &&
        a_observe_phase_q == ObserveIdle && b_observe_phase_q == ObserveIdle) begin
      cover_ready_q <= 1'b1;
    end

    if (a_rst_ni && b_rst_ni) begin
      if (cover_a_origin_q == CoverIdle && cover_ready_q &&
          clear_sequence_idle && a_clear_i && !b_clear_i) begin
        cover_a_origin_q <= CoverIsolate;
      end else if (cover_a_origin_q == CoverIsolate &&
                   a_isolate_o && b_isolate_o) begin
        cover_a_origin_q <= CoverClear;
      end else if (cover_a_origin_q == CoverClear &&
                   a_clear_o && b_clear_o) begin
        cover_a_origin_q <= CoverPostClear;
      end else if (cover_a_origin_q == CoverPostClear &&
                   a_isolate_o && b_isolate_o && !a_clear_o && !b_clear_o) begin
        cover_a_origin_q <= CoverReturnIdle;
      end else if (cover_a_origin_q == CoverReturnIdle && clear_sequence_idle) begin
        cover_a_origin_q <= CoverDone;
      end

      if (cover_b_origin_q == CoverIdle && cover_ready_q &&
          clear_sequence_idle && !a_clear_i && b_clear_i) begin
        cover_b_origin_q <= CoverIsolate;
      end else if (cover_b_origin_q == CoverIsolate &&
                   a_isolate_o && b_isolate_o) begin
        cover_b_origin_q <= CoverClear;
      end else if (cover_b_origin_q == CoverClear &&
                   a_clear_o && b_clear_o) begin
        cover_b_origin_q <= CoverPostClear;
      end else if (cover_b_origin_q == CoverPostClear &&
                   a_isolate_o && b_isolate_o && !a_clear_o && !b_clear_o) begin
        cover_b_origin_q <= CoverReturnIdle;
      end else if (cover_b_origin_q == CoverReturnIdle && clear_sequence_idle) begin
        cover_b_origin_q <= CoverDone;
      end

      if (cover_simultaneous_origin_q == CoverIdle && cover_ready_q &&
          clear_sequence_idle && a_clear_i && b_clear_i) begin
        cover_simultaneous_origin_q <= CoverIsolate;
      end else if (cover_simultaneous_origin_q == CoverIsolate &&
                   a_isolate_o && b_isolate_o) begin
        cover_simultaneous_origin_q <= CoverClear;
      end else if (cover_simultaneous_origin_q == CoverClear &&
                   a_clear_o && b_clear_o) begin
        cover_simultaneous_origin_q <= CoverPostClear;
      end else if (cover_simultaneous_origin_q == CoverPostClear &&
                   a_isolate_o && b_isolate_o && !a_clear_o && !b_clear_o) begin
        cover_simultaneous_origin_q <= CoverReturnIdle;
      end else if (cover_simultaneous_origin_q == CoverReturnIdle && clear_sequence_idle) begin
        cover_simultaneous_origin_q <= CoverDone;
      end
    end

    if (cover_a_origin_q == CoverDone) begin
      cover (1'b1);
    end

    if (cover_b_origin_q == CoverDone) begin
      cover (1'b1);
    end

    if (cover_simultaneous_origin_q == CoverDone) begin
      cover (1'b1);
    end

  end

endmodule
