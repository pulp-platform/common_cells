// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Vatsal Dixit <vdixit@student.ethz.ch>
// - Gianluca Bellocchi <gianluca.bellocchi@unimore.it>
//
// Description: Weighted round-robin arbiter.
//
// This module implements weighted round-robin arbitration among `NumIn` inputs that share one
// output channel. The output bandwidth is distributed among the inputs according to their weights
// (`weights_i`). Whenever input `i` wins arbitration, it performs up to `weights_i[i]` consecutive
// transfers, after which the arbiter grants access to the next contending input. Over a full
// arbitration round, input `i` therefore performs `weights_i[i]` out of `sum(weights_i)`
// transfers. The bandwidth share of each input is thus proportional to its weight. The higher the
// weight, the more bandwidth the input is granted. Every weight must be at least 1.
//
// A transfer is a generic valid/ready handshake on the output, so the unit of a weight depends on
// what the handshake represents. In this sense, the approach can be adapted to various arbitration
// use-cases, such as for a NoC packet or an AXI4 burst.
//
// Weighted round-robin is an extension of standard round-robin arbitration. Accordingly,
// `cc_wrr_arbiter` is built on top of `cc_rr_arb_tree`, which is used as an index generator. It
// decides which input wins the arbitration and holds that decision for the entire duration of the
// arbitration round. To this end, `cc_rr_arb_tree` is provided with a snapshot of the input
// contender set (`req_lock_q`) and its round-robin pointer only advances when an arbitration
// round ends (`end_arb`). It then outputs the index of the arbitration winner (`winner_idx`).

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module cc_wrr_arbiter #(
  // Number of request channels to arbitrate.
  parameter int unsigned NumIn       = 4,
  // Data width of the payload in bits. Not needed if `data_t` is overwritten.
  parameter int unsigned DataWidth   = 32,
  // Data type of the payload. It can be overwritten with a custom type.
  parameter type         data_t      = logic [DataWidth-1:0],
  // Width of the input weights. A weight may range from 1 to `2**WeightWidth-1`.
  // A weight of 0 is illegal.
  parameter int unsigned WeightWidth = 4,
  // Derived parameters, do **not** overwrite!
  //
  // Width of the arbitrated index.
  localparam int unsigned IdxWidth   = cc_pkg::idx_width(NumIn),
  // Type of the arbitrated index.
  localparam type         idx_t      = logic [IdxWidth-1:0]
) (
  input  logic                            clk_i,
  input  logic                            rst_ni,
  input  logic                            flush_i,
  // Input channels.
  input  logic    [NumIn-1:0]             req_i,
  output logic    [NumIn-1:0]             gnt_o,
  input  data_t   [NumIn-1:0]             data_i,
  // Input weights.
  input  logic    [NumIn-1:0][WeightWidth-1:0] weights_i,
  // Output channel.
  output logic                            req_o,
  input  logic                            gnt_i,
  output data_t                           data_o,
  // Index from which input the data came from.
  output idx_t                            idx_o,
  // Error flags for illegal weight values.
  output logic    [NumIn-1:0]             weight_error_o
);

  logic                   any_req;                // at least one input requests
  idx_t                   winner_idx;             // index of next arbitration winner
  logic [NumIn-1:0]       req_lock_q, req_lock_d; // current contender set

  logic                   start_arb;              // start of arbitration round
  logic                   early_end_arb;          // arbitration round ends before last transfer
  logic                   end_arb;                // end of arbitration round -> advance rr pointer
  logic                   end_arb_q,  end_arb_d;
  logic                   done_arb;               // last transfer of the round is accepted

  logic                   transfer;               // one output transfer
  logic                   last_transfer;          // last output transfer of arbitration round

  logic [WeightWidth-1:0] cnt_eff;                // remaining transfers in the current round
  logic [WeightWidth-1:0] cnt_q,      cnt_d;
  logic [WeightWidth-1:0] sel_weight;             // weight of arbitration winner

  //////////////////////
  // Winner selection //
  //////////////////////
  assign any_req = |req_i;

  // A new arbitration round starts when the arbiter is idle or when the previous round ended. In
  // both cases the round-robin arbiter is not locked, so a new contender set can be loaded safely.
  assign start_arb  = (~|req_lock_q) | end_arb_q;
  assign req_lock_d = start_arb ? req_i : req_lock_q;

  /////////////////////////
  // Round-robin arbiter //
  /////////////////////////
  cc_rr_arb_tree #(
    .NumIn     ( NumIn  ),
    .data_t    ( logic  ),
    .ExtPrio   ( 1'b0   ),
    .AxiVldRdy ( 1'b1   ),
    .LockIn    ( 1'b1   ),
    .FairArb   ( 1'b1   )
  ) i_cc_rr_arb_tree (
    .clk_i,
    .rst_ni,
    .flush_i ( flush_i      ),
    .rr_i    ( '0           ),
    .req_i   ( req_lock_d   ),
    .gnt_o   ( /* unused */ ),
    .data_i  ( '0           ),
    .req_o   ( /* unused */ ),
    .gnt_i   ( end_arb      ),
    .data_o  ( /* unused */ ),
    .idx_o   ( winner_idx   )
  );

  ////////////////////
  // Output control //
  ////////////////////
  // Guard the output index when no input requests.
  assign idx_o  = any_req ? winner_idx : '0;
  assign req_o  = any_req ? req_i[idx_o] : 1'b0;
  assign data_o = data_i[idx_o];

  always_comb begin : proc_gnt_o
    gnt_o = '0;
    if (req_o) gnt_o[idx_o] = gnt_i;
  end

  //////////////////////
  // Transfer counter //
  //////////////////////
  // Count the remaining transfers of the winner in the current arbitration round.
  assign transfer = req_o & gnt_i;

  // Weight of the current arbitration winner. If the winner has an illegal weight of 0, then
  // treat it as a weight of 1, so that the input gets consumed.
  assign sel_weight = weights_i[idx_o] | WeightWidth'(weights_i[idx_o] == '0);

  assign cnt_eff       = start_arb ? sel_weight : cnt_q;
  assign last_transfer = (cnt_eff == WeightWidth'(1));
  assign done_arb      = transfer & last_transfer;

  assign early_end_arb = (|req_lock_q) & ~req_i[winner_idx];
  assign end_arb       = done_arb | early_end_arb;

  // Decrement on each transfer. Hold during stalls and idle cycles.
  assign cnt_d     = transfer ? (cnt_eff - WeightWidth'(1)) : cnt_eff;
  assign end_arb_d = end_arb;

  `FFARNC(req_lock_q, req_lock_d, flush_i, '0,   clk_i, rst_ni)
  `FFARNC(end_arb_q,  end_arb_d,  flush_i, 1'b0, clk_i, rst_ni)
  `FFARNC(cnt_q,      cnt_d,      flush_i, '0,   clk_i, rst_ni)

  ///////////////////
  // Error control //
  ///////////////////
  for (genvar i = 0; i < NumIn; i++) begin : gen_weight_error
    assign weight_error_o[i] = (weights_i[i] == '0);
  end

  ////////////////
  // Assertions //
  ////////////////
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(numin_0, NumIn >= 1, "Need at least one input.")
  `ASSERT(req_implies_input, req_o |-> |req_i, clk_i, !rst_ni || flush_i,
          "Output valid must imply at least one input valid.")
  `ASSERT(gnt_onehot, $onehot0(gnt_o), clk_i, !rst_ni || flush_i,
          "Grant must be one-hot or zero.")
  `ASSERT(gnt_implies_req, |gnt_o |-> gnt_i, clk_i, !rst_ni || flush_i,
          "A grant out implies the downstream granted in.")
  for (genvar i = 0; i < NumIn; i++) begin : gen_weight_assumptions
    `ASSUME(weight_nonzero, weights_i[i] != '0, clk_i, !rst_ni,
            $sformatf("Weight of input %0d is 0, which is illegal.", i))
  end
  `ASSUME(flush_not_stalled, flush_i |-> !(req_o && !gnt_i), clk_i, !rst_ni,
          "Flush while an output transfer is pending.")
  `endif

endmodule
