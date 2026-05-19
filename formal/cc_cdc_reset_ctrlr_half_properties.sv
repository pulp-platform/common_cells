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
  parameter logic CLEAR_ON_ASYNC_RESET = 1'b1
)(
  input wire       clk_i,
  input wire       rst_ni,
  input wire       clear_i,
  input wire       isolate_o,
  input wire       isolate_ack_i,
  input wire       clear_o,
  input wire       clear_ack_i,
  input wire [1:0] async_next_phase_o,
  input wire       async_req_o,
  input wire [1:0] async_next_phase_i,
  input wire       async_req_i,
  input wire       async_ack_o,
  input wire [3:0] initiator_state_q,
  input wire       initiator_phase_transition_ack,
  input wire [1:0] initiator_clear_seq_phase,
  input wire       initiator_phase_transition_req,
  input wire       initiator_isolate_out,
  input wire       initiator_clear_out,
  input wire [1:0] receiver_phase_q,
  input wire [1:0] receiver_next_phase,
  input wire       receiver_phase_req,
  input wire       receiver_phase_ack,
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

  function automatic logic valid_phase(input logic [1:0] phase);
    case (phase)
      PhaseIdle, PhaseIsolate, PhaseClear, PhasePostClear: valid_phase = 1'b1;
      default: valid_phase = 1'b0;
    endcase
  endfunction

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

  // Reset modeling: force the first sampled cycle into reset so the proof starts
  // from a reachable reset-controller half state.
  always_ff @(posedge clk_i) begin
    init_q <= 1'b1;
    if (!init_q) begin
      assume (!rst_ni);
    end
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
    end

    if (rst_ni) begin
      assert (clear_o == (initiator_clear_out || receiver_clear_out));
      assert (isolate_o == (initiator_isolate_out || receiver_isolate_out));
      assert (!clear_o || isolate_o);
      assert (!initiator_clear_out || initiator_isolate_out);
      assert (!receiver_clear_out || receiver_isolate_out);

      assert (valid_initiator_state(initiator_state_q));
      assert (valid_phase(receiver_phase_q));

      if (async_req_o) begin
        assert (valid_phase(async_next_phase_o));
      end

      if (initiator_phase_transition_req) begin
        assert (valid_phase(initiator_clear_seq_phase));
      end

      if (receiver_phase_req) begin
        assume (valid_phase(receiver_next_phase));

        case (receiver_next_phase)
          PhaseIdle: begin
            assert (!receiver_clear_out);
            assert (!receiver_isolate_out);
            assert (receiver_phase_ack);
          end
          PhaseIsolate: begin
            assert (!receiver_clear_out);
            assert (receiver_isolate_out);
            assert (receiver_phase_ack == isolate_ack_i);
          end
          PhaseClear: begin
            assert (receiver_clear_out);
            assert (receiver_isolate_out);
            assert (receiver_phase_ack == clear_ack_i);
          end
          PhasePostClear: begin
            assert (!receiver_clear_out);
            assert (receiver_isolate_out);
            assert (receiver_phase_ack);
          end
          default: begin
          end
        endcase
      end else begin
        case (receiver_phase_q)
          PhaseIdle: begin
            assert (!receiver_clear_out);
            assert (!receiver_isolate_out);
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
      end
    end
  end

  // Sequential local-state checks. These assert the output contract of each
  // initiator state and require stalled receiver phases to stay stable.
  always_ff @(posedge clk_i) begin
    if (rst_ni && init_q) begin
      if (receiver_phase_req && !receiver_phase_ack) begin
        assume (receiver_next_phase == $past(receiver_next_phase));
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

    // Cover the main local and remote clear phases
    // so bounded runs exercise both sides of the bidirectional half.
    cover (rst_ni && initiator_state_q == InitClear);
    cover (rst_ni && initiator_state_q == InitPostClear);
    cover (rst_ni && receiver_phase_q == PhaseClear);
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
  .async_next_phase_o,
  .async_req_o,
  .async_next_phase_i,
  .async_req_i,
  .async_ack_o,
  .initiator_state_q,
  .initiator_phase_transition_ack,
  .initiator_clear_seq_phase,
  .initiator_phase_transition_req,
  .initiator_isolate_out,
  .initiator_clear_out,
  .receiver_phase_q,
  .receiver_next_phase,
  .receiver_phase_req,
  .receiver_phase_ack,
  .receiver_isolate_out,
  .receiver_clear_out
);
