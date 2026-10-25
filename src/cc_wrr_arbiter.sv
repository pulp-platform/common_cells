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
// what the handshake represents, e.g., a flit, a NoC packet, or an AXI4 burst.
//
// Weighted round-robin is an extension of standard round-robin arbitration. Accordingly,
// `cc_wrr_arbiter` is built on top of `cc_rr_arb_tree`, which decides which input wins the
// arbitration and holds that decision for the entire duration of the weight window.

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
  output idx_t                            idx_o
);

  // ---------------------------------------------------------------------------------------------
  // Winner selection: reuse the fair round-robin tree purely as an index generator.
  // ---------------------------------------------------------------------------------------------
  // The inner arbiter is fed a *snapshot* of the contender set and its pointer only advances when
  // we pulse its `gnt_i` (once per completed burst). It therefore tells us *who* the current
  // winner is and holds that choice stable for the duration of the burst.
  idx_t                 winner_idx;
  logic                 any_req;
  logic [NumIn-1:0]     eff_req;                // requesting AND non-zero weight -> may contend

  logic [NumIn-1:0]     req_lock_q, req_lock_d; // snapshot of the contenders for the current round
  logic                 done_q,     done_d;     // registered "previous flit completed a burst"
  logic [WtWidth-1:0]   cnt_q,      cnt_d;      // remaining flits in the current burst
  logic [WtWidth-1:0]   cnt_eff;                // effective remaining count this cycle
  logic [WtWidth-1:0]   sel_weight;             // weight of the current winner (always >= 1)

  logic                 load_round;             // (re)load snapshot + weight for a fresh burst
  logic                 flit_transfered;        // one accepted transfer (flit) from current winner
  logic                 last_flit;              // this flit is the last of the current burst
  logic                 burst_done;             // last flit accepted -> advance the rr pointer
  logic                 winner_gone;            // locked winner quit requesting (e.g. QoS-masked)
  logic                 round_end;              // burst done OR winner abandoned -> re-arbitrate

  // A weight of 0 means "no bandwidth": that input is excluded from arbitration entirely (skipped,
  // never granted) instead of being served. Only requesting inputs with a non-zero weight contend,
  // which also guarantees the burst counter never loads 0.
  always_comb begin : proc_eff_req
    for (int unsigned i = 0; i < NumIn; i++) eff_req[i] = req_i[i] & (weights_i[i] != '0);
  end

  assign any_req = |eff_req;

  // A fresh burst is loaded when the arbiter is idle (no snapshot held) or the previous flit
  // finished a burst. On both of these cycles the inner arbiter's LockIn is disengaged, so it is
  // safe to present it a fresh (possibly changed) request vector here.
  assign load_round = (~|req_lock_q) | done_q; // no request pending OR this round complete
  assign req_lock_d = load_round ? eff_req : req_lock_q;

  cc_rr_arb_tree #(
    .NumIn     ( NumIn  ),
    .data_t    ( logic  ), // inner arbiter is used for the index only; data is muxed externally
    .ExtPrio   ( 1'b0   ),
    .AxiVldRdy ( 1'b1   ),
    .LockIn    ( 1'b1   ), // hold the winning index for the whole burst
    .FairArb   ( 1'b1   )  // fair rotation across bursts
  ) i_cc_rr_arb_tree (
    .clk_i,
    .rst_ni,
    .flush_i ( flush_i      ),
    .rr_i    ( '0           ),
    .req_i   ( req_lock_d   ), // stable contender snapshot
    .gnt_o   ( /* unused */ ),
    .data_i  ( '0           ),
    .req_o   ( /* unused */ ),
    .gnt_i   ( round_end    ), // advance the pointer when a burst completes or is abandoned
    .data_o  ( /* unused */ ),
    .idx_o   ( winner_idx   )
  );

  // ---------------------------------------------------------------------------------------------
  // Output handshake / data: muxed from the current winner.
  // ---------------------------------------------------------------------------------------------
  assign idx_o  = any_req ? winner_idx : '0;
  assign req_o  = any_req ? req_i[idx_o] : 1'b0;
  assign data_o = data_i[idx_o];

  always_comb begin : proc_gnt_o
    gnt_o = '0;
    // Grant the winner only when its flit actually transfers (output valid AND downstream ready).
    // Gating on `req_o` (not just `gnt_i`) matters when the winner was masked out mid-burst by an
    // upstream stage (e.g. cc_qos_wrr_arbiter): without it the winner would get a spurious grant for
    // a flit that never leaves, dropping data. Under saturation req_o is always 1, so this is a
    // no-op there.
    if (req_o) gnt_o[idx_o] = gnt_i;
  end

  // ---------------------------------------------------------------------------------------------
  // Burst counter.
  // ---------------------------------------------------------------------------------------------
  assign flit_transfered = req_o & gnt_i;

  // idx_o is always an eligible (non-zero-weight) winner, so this weight is >= 1.
  assign sel_weight = weights_i[idx_o];

  // On a load cycle the count starts at the winner's weight; otherwise it is the running value.
  assign cnt_eff    = load_round ? sel_weight : cnt_q;
  assign last_flit  = (cnt_eff == WtWidth'(1));
  assign burst_done = flit_transfered & last_flit;

  // Abandon the current burst if the locked winner stops requesting (e.g. it was masked out by an
  // upstream QoS/priority stage). Without this the arbiter stays locked on a winner that can no
  // longer present a flit and stalls forever; abandoning keeps it work-conserving and lets the next
  // contender win. Under saturated traffic the winner never withdraws mid-burst, so `winner_gone`
  // never fires and behaviour is unchanged. (A downstream stall keeps the winner requesting, so it
  // does NOT abandon - only an actual withdrawal does.)
  assign winner_gone = (|req_lock_q) & ~eff_req[winner_idx];
  assign round_end   = burst_done | winner_gone;

  // Decrement only on an accepted flit; hold otherwise (covers downstream stalls and bubbles).
  assign cnt_d  = flit_transfered ? (cnt_eff - WtWidth'(1)) : cnt_eff;
  assign done_d = round_end;

  `FFARNC(req_lock_q, req_lock_d, flush_i, '0,   clk_i, rst_ni)
  `FFARNC(done_q,     done_d,     flush_i, 1'b0, clk_i, rst_ni)
  `FFARNC(cnt_q,      cnt_d,      flush_i, '0,   clk_i, rst_ni)

  // ---------------------------------------------------------------------------------------------
  // Assertions.
  // ---------------------------------------------------------------------------------------------
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(numin_0, NumIn >= 1, "Need at least one input.")
  `ASSERT(req_implies_input, req_o |-> |req_i, clk_i, !rst_ni || flush_i,
          "Output valid must imply at least one input valid.")
  `ASSERT(gnt_onehot, $onehot0(gnt_o), clk_i, !rst_ni || flush_i,
          "Grant must be one-hot or zero.")
  `ASSERT(gnt_implies_req, |gnt_o |-> gnt_i, clk_i, !rst_ni || flush_i,
          "A grant out implies the downstream granted in.")
  `ASSERT(no_zero_weight_grant, |gnt_o |-> (weights_i[idx_o] != '0), clk_i, !rst_ni || flush_i,
          "A zero-weight input must never be granted.")
  `endif

endmodule
