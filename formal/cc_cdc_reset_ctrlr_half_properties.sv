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
// Description: Reset-Controller Half Properties
// Prove the local clear/isolate FSM contract of one reset-controller half,
// including phase decode, output consistency, and initiator state transitions.

module cc_cdc_reset_ctrlr_half_properties #(
  parameter logic CLEAR_ON_ASYNC_RESET = 1'b1,
`ifdef CC_CDC_RESET_CTRLR_ASSUME_REMOTE_PHASE
  parameter logic ASSUME_REMOTE_PHASE = 1'b1
`else
  parameter logic ASSUME_REMOTE_PHASE = 1'b0
`endif
)(
  input wire       clk_i,
  input wire       rst_ni,
  input wire       clear_i,
  input wire       isolate_o,
  input wire       isolate_ack_i,
  input wire       clear_o,
  input wire       clear_ack_i,
  input wire [3:0] initiator_state_q,
  input wire       initiator_phase_transition_ack,
  input wire [1:0] initiator_clear_seq_phase,
  input wire       initiator_phase_transition_req,
  input wire       initiator_isolate_out,
  input wire       initiator_clear_out,
  input wire [1:0] receiver_phase_q,
  input wire [1:0] receiver_effective_phase,
  input wire [1:0] receiver_next_phase,
  input wire       receiver_phase_req,
  input wire       receiver_phase_ack,
  input wire       receiver_phase_pending_q,
  input wire       receiver_phase_done_q,
  input wire       receiver_capture_phase,
  input wire       receiver_isolate_out,
  input wire       receiver_clear_out
);

  localparam logic [1:0] PhaseIdle      = 2'd0;
  localparam logic [1:0] PhaseIsolate   = 2'd1;
  localparam logic [1:0] PhaseClear     = 2'd2;
  localparam logic [1:0] PhasePostClear = 2'd3;

  localparam logic [3:0] InitIdle                = 4'd0;
  localparam logic [3:0] InitIsolate             = 4'd1;
  localparam logic [3:0] InitWaitIsolatePhaseAck = 4'd2;
  localparam logic [3:0] InitWaitIsolateAck      = 4'd3;
  localparam logic [3:0] InitClear               = 4'd4;
  localparam logic [3:0] InitWaitClearPhaseAck   = 4'd5;
  localparam logic [3:0] InitWaitClearAck        = 4'd6;
  localparam logic [3:0] InitPostClear           = 4'd7;
  localparam logic [3:0] InitFinished            = 4'd8;

  function automatic logic valid_initiator_state(input logic [3:0] state);
    case (state)
      InitIdle,
      InitIsolate,
      InitWaitIsolatePhaseAck,
      InitWaitIsolateAck,
      InitClear,
      InitWaitClearPhaseAck,
      InitWaitClearAck,
      InitPostClear,
      InitFinished: valid_initiator_state = 1'b1;
      default: valid_initiator_state = 1'b0;
    endcase
  endfunction

  logic init_q = 1'b0;

  // The remote phase is an ordered, acknowledged protocol.  Keep the
  // captured phase separately so a CLEAR capture cannot skip an
  // unacknowledged ISOLATE phase.
  logic [1:0] remote_acked_phase_q      = PhaseIdle;
  logic [1:0] remote_captured_phase_q   = PhaseIdle;
  logic       remote_capture_pending_q = 1'b0;

  localparam logic [2:0] ReceiverCoverIdle       = 3'd0;
  localparam logic [2:0] ReceiverCoverIsolate    = 3'd1;
  localparam logic [2:0] ReceiverCoverClear      = 3'd2;
  localparam logic [2:0] ReceiverCoverPostClear  = 3'd3;
  localparam logic [2:0] ReceiverCoverReturnIdle = 3'd4;
  localparam logic [2:0] ReceiverCoverDone       = 3'd5;
  logic [2:0] receiver_cover_q = ReceiverCoverIdle;

  // Reset modeling: force the first sampled cycle into reset, then defer later
  // asynchronous reset assertions to a separate reset model.
  always_ff @(posedge clk_i) begin
    if (!init_q) begin
      assume (!rst_ni);
    end else begin
      assume (rst_ni);
    end
    init_q <= 1'b1;
  end

  // Combinational contract: These checks tie the public clear/isolate
  // outputs to the initiator/receiver halves and validate receiver phase decode.
  always_comb begin
    if (!rst_ni) begin
      if (CLEAR_ON_ASYNC_RESET) begin
        assert (initiator_state_q == InitIsolate);
      end else begin
        assert (initiator_state_q == InitIdle);
      end
      assert (receiver_phase_q == PhaseIdle);
      assert (receiver_effective_phase == PhaseIdle);
    end

    if (rst_ni) begin
      assert (!clear_o || isolate_o);
      assert (valid_initiator_state(initiator_state_q));

      case (receiver_effective_phase)
        PhaseIdle: begin
          assert (!receiver_clear_out);
          // The receiver raises isolation for the capture cycle before the
          // registered phase is updated.  Idle is de-isolated otherwise.
          if (!receiver_capture_phase) begin
            assert (!receiver_isolate_out);
          end
        end
        PhaseIsolate: begin
          assert (!receiver_clear_out);
          assert (receiver_isolate_out);
        end
        PhaseClear: begin
          assert (receiver_clear_out);
          assert (receiver_isolate_out);
        end
        PhasePostClear: begin
          assert (!receiver_clear_out);
          assert (receiver_isolate_out);
        end
        default: begin
        end
      endcase

      if (receiver_phase_ack) begin
        assert (receiver_phase_pending_q);
        if (receiver_effective_phase == PhaseIsolate)
          assert (isolate_ack_i);
        if (receiver_effective_phase == PhaseClear)
          assert (clear_ack_i);
      end

    end
  end

  // Sequential local-state checks. These assert the output contract of each
  // initiator state and require stalled receiver phases to stay stable.
  always_ff @(posedge clk_i) begin
    if (rst_ni && init_q) begin
      if ($past(rst_ni && receiver_phase_req && !receiver_phase_ack)) begin
        if (ASSUME_REMOTE_PHASE) begin
          assume (receiver_phase_req);
          assume (receiver_next_phase == $past(receiver_next_phase));
        end else begin
          assert (receiver_phase_req);
          assert (receiver_next_phase == $past(receiver_next_phase));
        end
      end

      // Receiver transaction state is sampled one cycle after each DUT
      // transition.  Guard every past-value check with both reset samples so
      // the initial reset message is not mistaken for a normal transaction.
      if ($past(rst_ni) && $past(receiver_capture_phase)) begin
        assert (receiver_phase_pending_q);
        assert (receiver_phase_q == $past(receiver_next_phase));
      end

      if ($past(rst_ni && receiver_phase_pending_q && !receiver_phase_ack)) begin
        assert (receiver_phase_pending_q);
        assert (receiver_phase_q == $past(receiver_phase_q));
      end

      if ($past(rst_ni && receiver_phase_ack)) begin
        assert (!receiver_phase_pending_q);
      end

      if (receiver_phase_done_q) begin
        assert (!receiver_capture_phase);
      end

      if (receiver_phase_pending_q) begin
        assert (!receiver_capture_phase);
      end

      if ($past(rst_ni && !receiver_phase_req)) begin
        assert (!receiver_phase_done_q);
      end

      if (initiator_state_q == InitIdle) begin
        assert (!initiator_isolate_out);
        assert (!initiator_clear_out);
        assert (!initiator_phase_transition_req);
      end

      if (initiator_state_q == InitIsolate ||
          initiator_state_q == InitWaitIsolatePhaseAck) begin
        assert (initiator_isolate_out);
        assert (!initiator_clear_out);
        assert (initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhaseIsolate);
      end

      if (initiator_state_q == InitWaitIsolateAck) begin
        assert (initiator_isolate_out);
        assert (!initiator_clear_out);
        assert (!initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhaseIsolate);
      end

      if (initiator_state_q == InitClear ||
          initiator_state_q == InitWaitClearPhaseAck) begin
        assert (initiator_isolate_out);
        assert (initiator_clear_out);
        assert (initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhaseClear);
      end

      if (initiator_state_q == InitWaitClearAck) begin
        assert (initiator_isolate_out);
        assert (initiator_clear_out);
        assert (!initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhaseClear);
      end

      if (initiator_state_q == InitPostClear) begin
        assert (initiator_isolate_out);
        assert (!initiator_clear_out);
        assert (initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhasePostClear);
      end

      if (initiator_state_q == InitFinished) begin
        assert (initiator_isolate_out);
        assert (!initiator_clear_out);
        assert (initiator_phase_transition_req);
        assert (initiator_clear_seq_phase == PhaseIdle);
      end
    end

    // Initiator transition relation: the next state must match the previous
    // clear request, phase-CDC acknowledgement, and local isolate/clear ack.
    if (rst_ni && $past(rst_ni) && init_q) begin
      case ($past(initiator_state_q))
        InitIdle: begin
          assert (initiator_state_q == ($past(clear_i) ? InitIsolate : InitIdle));
        end
        InitIsolate: begin
          if ($past(initiator_phase_transition_ack && isolate_ack_i)) begin
            assert (initiator_state_q == InitClear);
          end else if ($past(initiator_phase_transition_ack)) begin
            assert (initiator_state_q == InitWaitIsolateAck);
          end else if ($past(isolate_ack_i)) begin
            assert (initiator_state_q == InitWaitIsolatePhaseAck);
          end else begin
            assert (initiator_state_q == InitIsolate);
          end
        end
        InitWaitIsolateAck: begin
          assert (initiator_state_q ==
                  ($past(isolate_ack_i) ? InitClear : InitWaitIsolateAck));
        end
        InitWaitIsolatePhaseAck: begin
          assert (initiator_state_q ==
                  ($past(initiator_phase_transition_ack) ? InitClear :
                                                           InitWaitIsolatePhaseAck));
        end
        InitClear: begin
          if ($past(initiator_phase_transition_ack && clear_ack_i)) begin
            assert (initiator_state_q == InitPostClear);
          end else if ($past(initiator_phase_transition_ack)) begin
            assert (initiator_state_q == InitWaitClearAck);
          end else if ($past(clear_ack_i)) begin
            assert (initiator_state_q == InitWaitClearPhaseAck);
          end else begin
            assert (initiator_state_q == InitClear);
          end
        end
        InitWaitClearAck: begin
          assert (initiator_state_q ==
                  ($past(clear_ack_i) ? InitPostClear : InitWaitClearAck));
        end
        InitWaitClearPhaseAck: begin
          assert (initiator_state_q ==
                  ($past(initiator_phase_transition_ack) ? InitPostClear :
                                                           InitWaitClearPhaseAck));
        end
        InitPostClear: begin
          assert (initiator_state_q ==
                  ($past(initiator_phase_transition_ack) ? InitFinished : InitPostClear));
        end
        InitFinished: begin
          assert (initiator_state_q ==
                  ($past(initiator_phase_transition_ack) ? InitIdle : InitFinished));
        end
        default: begin
          assert (initiator_state_q == InitIsolate);
        end
      endcase
    end

    // Constrain the remote phase order only in the standalone half proof; in
    // the composed proof the opposite half supplies that protocol.  Tracking
    // consistency remains asserted in both configurations.
    if (!rst_ni) begin
      remote_acked_phase_q      <= PhaseIdle;
      remote_captured_phase_q   <= PhaseIdle;
      remote_capture_pending_q  <= 1'b0;
    end else begin
      if (receiver_capture_phase) begin
        if (ASSUME_REMOTE_PHASE) begin
          case (remote_acked_phase_q)
            PhaseIdle:      assume (receiver_next_phase == PhaseIsolate);
            PhaseIsolate:   assume (receiver_next_phase == PhaseClear);
            PhaseClear:     assume (receiver_next_phase == PhasePostClear);
            PhasePostClear: assume (receiver_next_phase == PhaseIdle);
            default:        assume (1'b0);
          endcase
        end
        remote_captured_phase_q  <= receiver_next_phase;
        remote_capture_pending_q <= 1'b1;
      end

      if (receiver_phase_ack) begin
        assert (remote_capture_pending_q);
        assert (receiver_phase_q == remote_captured_phase_q);
        remote_acked_phase_q     <= receiver_phase_q;
        remote_capture_pending_q <= 1'b0;
      end
    end

    // Complete remote accepted cycle: IDLE -> ISOLATE -> CLEAR -> POST_CLEAR
    // -> IDLE, including request withdrawal after the final acknowledge.
    if (!rst_ni) begin
      receiver_cover_q <= ReceiverCoverIdle;
    end else begin
      case (receiver_cover_q)
        ReceiverCoverIdle:
          if (receiver_phase_ack && receiver_phase_q == PhaseIsolate)
            receiver_cover_q <= ReceiverCoverIsolate;
        ReceiverCoverIsolate:
          if (receiver_phase_ack && receiver_phase_q == PhaseClear)
            receiver_cover_q <= ReceiverCoverClear;
        ReceiverCoverClear:
          if (receiver_phase_ack && receiver_phase_q == PhasePostClear)
            receiver_cover_q <= ReceiverCoverPostClear;
        ReceiverCoverPostClear:
          if (receiver_phase_ack && receiver_phase_q == PhaseIdle)
            receiver_cover_q <= ReceiverCoverReturnIdle;
        ReceiverCoverReturnIdle:
          if (!receiver_phase_req)
            receiver_cover_q <= ReceiverCoverDone;
        default: begin
        end
      endcase
    end

`ifndef CC_CDC_RESET_CTRLR_SKIP_HALF_COVERS
    // Keep initiator sequence, wait/backpressure, and return-to-idle evidence.
    cover (rst_ni && initiator_state_q == InitClear);
    cover (rst_ni && initiator_state_q == InitPostClear);
    cover (rst_ni && initiator_state_q == InitWaitIsolatePhaseAck);
    cover (rst_ni && initiator_state_q == InitWaitIsolateAck);
    cover (rst_ni && initiator_state_q == InitWaitClearPhaseAck);
    cover (rst_ni && initiator_state_q == InitWaitClearAck);
    cover (rst_ni && initiator_phase_transition_req &&
           !initiator_phase_transition_ack);
    cover (rst_ni && receiver_phase_pending_q && receiver_phase_req &&
           !receiver_phase_ack);
    cover (rst_ni && $past(rst_ni) && init_q &&
           $past(initiator_state_q == InitFinished &&
                 initiator_phase_transition_ack) &&
           initiator_state_q == InitIdle);
    cover (rst_ni && receiver_cover_q == ReceiverCoverDone);
`endif
  end

endmodule


bind cc_cdc_reset_ctrlr_half cc_cdc_reset_ctrlr_half_properties #(
  .CLEAR_ON_ASYNC_RESET(ClearOnAsyncReset)
) i_cc_cdc_reset_ctrlr_half_properties (
  .clk_i,
  .rst_ni,
  .clear_i,
  .isolate_o,
  .isolate_ack_i,
  .clear_o,
  .clear_ack_i,
  .initiator_state_q,
  .initiator_phase_transition_ack,
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
  .receiver_phase_done_q,
  .receiver_capture_phase,
  .receiver_isolate_out,
  .receiver_clear_out
);
