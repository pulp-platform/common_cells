// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.08.2018
// Description: Round robin arbiter with lookahead
//
// this unit is a generic round robin arbiter with "look ahead" - i.e. it jumps
// to the next valid request signal instead of stepping around with stepsize 1.
// if the current req signal has been acknowledged in the last cycle, and it is
// again valid in the current cycle, the arbiter will first serve the other req
// signals (if there is a valid one) in the req vector before acknowledging the
// same signal again (this prevents starvation).
//
// the arbiter has a request signal vector input (req_i) and an ack
// signal vector ouput (ack_o). to enable the arbiter the signal
// en_i has to be asserted. vld_o is high when one of the req_i signals is
// acknowledged.
//
// the entity has one register which stores the index of the last request signal
// that was served.
//
// the lock-in feature prevents the arbiter from changing the arbitration decision
// when the arbiter is disabled - i.e., the index of the first request that wins the
// arbitration will be locked until en_i is asserted again.
//
// dependencies: relies on fast leading zero counter tree "lzc" in common_cells

module rrarbiter #(
  parameter int unsigned NUM_REQ = 13,
  parameter int unsigned LOCK_IN = 0
) (
  input logic                         clk_i,
  input logic                         rst_ni,

  input logic                         flush_i, // clears the fsm and control signal registers
  input logic                         en_i,    // arbiter enable
  input logic [NUM_REQ-1:0]           req_i,   // request signals

  output logic [NUM_REQ-1:0]          ack_o,   // acknowledge signals
  output logic                        vld_o,   // request ack'ed
  output logic [$clog2(NUM_REQ)-1:0]  idx_o    // idx output
);

  localparam SEL_WIDTH = $clog2(NUM_REQ);

  logic [SEL_WIDTH-1:0] arb_sel_d, arb_sel_q;
  logic [SEL_WIDTH-1:0] arb_sel_lock_d, arb_sel_lock_q;


  // only used in case of more than 2 requesters
  logic [NUM_REQ-1:0] mask_lut[NUM_REQ-1:0];
  logic [NUM_REQ-1:0] mask;
  logic [NUM_REQ-1:0] masked_lower;
  logic [NUM_REQ-1:0] masked_upper;
  logic [SEL_WIDTH-1:0] lower_idx;
  logic [SEL_WIDTH-1:0] upper_idx;
  logic [SEL_WIDTH-1:0] next_idx;
  logic no_lower_ones;
  logic lock_d, lock_q;

  // shared
  assign idx_o          = arb_sel_d;
  assign vld_o          = (|req_i) & en_i;

  if (LOCK_IN > 0) begin : g_lock_in
    // latch decision in case we got at least one req and no acknowledge
    assign lock_d         = (|req_i) & ~en_i;
    assign arb_sel_lock_d = arb_sel_d;
  end else begin
    // disable
    assign lock_d         = '0;
    assign arb_sel_lock_d = '0;
  end

  // only 2 input requesters
  if (NUM_REQ == 2 && !LOCK_IN) begin : g_rrlogic

    assign arb_sel_d = (( arb_sel_q) | (~arb_sel_q & ~req_i[0])) & req_i[1];
    assign ack_o[0]  = ((~arb_sel_q) | ( arb_sel_q & ~req_i[1])) & req_i[0] & en_i;
    assign ack_o[1]  = arb_sel_d                                            & en_i;

  end else begin

    // this mask is used to mask the incoming req vector
    // depending on the index of the last served index
    assign mask = mask_lut[arb_sel_q];

    // get index from masked vectors
    lzc #(
        .WIDTH ( NUM_REQ )
    ) i_lower_ff1 (
        .in_i    ( masked_lower  ),
        .cnt_o   ( lower_idx     ),
        .empty_o ( no_lower_ones )
    );

    lzc #(
        .WIDTH ( NUM_REQ )
    ) i_upper_ff1 (
        .in_i    ( masked_upper  ),
        .cnt_o   ( upper_idx     ),
        .empty_o (               )
    );

    // wrap around
    assign next_idx   = (no_lower_ones)      ? upper_idx      :
                                               lower_idx;
    assign arb_sel_d  = (lock_q)             ? arb_sel_lock_q :
                        (next_idx < NUM_REQ) ? next_idx       :
                                               unsigned'(NUM_REQ-1);
  end

  for (genvar k=0; (k < NUM_REQ) && (NUM_REQ > 2 || LOCK_IN); k++) begin : g_mask
    assign mask_lut[k]     = unsigned'(2**(k+1)-1);
    assign masked_lower[k] = (~mask[k]) & req_i[k];
    assign masked_upper[k] = mask[k]    & req_i[k];
    assign ack_o[k]        = ((arb_sel_d == k) && vld_o );
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if(~rst_ni) begin
      arb_sel_q      <= '0;
      lock_q         <= 1'b0;
      arb_sel_lock_q <= '0;
    end else begin
      if (flush_i) begin
        arb_sel_q      <= '0;
        lock_q         <= 1'b0;
        arb_sel_lock_q <= '0;
      end else begin
        lock_q         <= lock_d;
        arb_sel_lock_q <= arb_sel_lock_d;

        if (vld_o) begin
          arb_sel_q    <= arb_sel_d;
        end
      end
    end
  end

// pragma translate_off
`ifndef VERILATOR
    // check parameterization, enable and hot1 property of acks
    // todo: check RR fairness with sequence assertion
    initial begin : p_assertions
      assert (NUM_REQ>=2) else $fatal ("minimum input width of req vecor is 2");
    end
    ack_implies_vld: assert property (@(posedge clk_i) disable iff (~rst_ni) |ack_o |-> vld_o)
      else $fatal (1,"an asserted ack signal implies that vld_o must be asserted, too");

    vld_implies_ack: assert property (@(posedge clk_i) disable iff (~rst_ni) vld_o  |-> |ack_o)
      else $fatal (1,"an asserted vld_o signal implies that one ack_o must be asserted, too");

    en_vld_check:    assert property (@(posedge clk_i) disable iff (~rst_ni) !en_i  |-> !vld_o)
      else $fatal (1,"vld must not be asserted when arbiter is disabled");

    en_ack_check:    assert property (@(posedge clk_i) disable iff (~rst_ni) !en_i  |-> !ack_o)
      else $fatal (1,"ack_o must not be asserted when arbiter is disabled");

    ack_idx_check:   assert property (@(posedge clk_i) disable iff (~rst_ni) vld_o |-> ack_o[idx_o])
      else $fatal (1,"index / ack_o do not match");

    hot1_check:      assert property (@(posedge clk_i) disable iff (~rst_ni) ((~(1<<idx_o)) & ack_o) == 0 )
      else $fatal (1,"only one ack_o can be asserted at a time (i.e. ack_o must be hot1)");
`endif
// pragma translate_on

endmodule : rrarbiter



