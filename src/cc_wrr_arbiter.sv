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
// Authors: Vatsal Dixit <vdixit@student.ethz.ch>
//          Gianluca Bellocchi <gianluca.bellocchi@unimore.it>
// Description: Weighted round-robin (WRR) arbiter.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

/// # Weighted Round-Robin Arbiter (`cc_wrr_arbiter`)
///
/// A generic, N-input arbiter that merges `NumIn` valid/ready input streams onto a single
/// valid/ready output stream while distributing the output bandwidth *proportionally to a
/// per-input weight* `weights_i[i]`. Under saturation (every input always requesting) input
/// `i` receives a steady-state share of
///
///     bandwidth_i = w_i / sum_j(w_j)        (j over all currently-contending inputs)
///
/// This is the knob the WRRA exposes: a requester with a higher weight `w_i` is granted more
/// of the shared link, which is exactly what is needed to counteract *topological unfairness*
/// in a NoC. When a chain/tree of these arbiters merges traffic towards a common destination,
/// setting each input's weight to the number of original requesters it aggregates restores
/// global fairness (each leaf source ends up with an equal share, regardless of how many hops
/// deep it sits). Weights are additive up the tree, so the same cell composes at any radix.
///
/// ## Mechanism: deficit / burst weighted round-robin
///
/// The weight is realised as a *burst*: when an input wins arbitration it is granted up to
/// `w_i` consecutive flits (one flit = one valid/ready transfer) before the round-robin pointer
/// advances to the next contender. Over a full rotation that visits every contender once, input
/// `i` therefore emits `w_i` out of `sum_j(w_j)` flits, giving the bandwidth split above.
///
/// Design decisions (and their trade-offs):
/// * **Reuse `cc_rr_arb_tree` for winner selection.** The inner arbiter (with `FairArb` and
///   `LockIn`) decides *who* wins and *holds that decision* for the whole burst; the wrra cell only
///   adds the burst counter on top. The inner `gnt_i` is pulsed exactly once per burst (on the
///   last accepted flit) so the inner round-robin pointer moves once per burst, not once per
///   flit. We feed the inner arbiter a *snapshot* of the contender set (`req_lock_q`) that is held
///   stable for the whole burst, which keeps the `LockIn` decision stable even if a non-winning
///   input deasserts, and avoids tripping the inner arbiter's `LockIn` assumptions.
/// * **Burst vs. interleaved.** A burst arbiter is small and simple but makes the output bursty:
///   a low-weight input may wait through a full high-weight burst, so its *latency/jitter* is
///   worse than with a (more expensive) interleaved/WFQ-style scheme. The bandwidth ratio is
///   identical either way, so for bandwidth shaping under contention the burst scheme is chosen.
/// * **The burst length is a *maximum*, not a guarantee of work.** A burst advances on accepted
///   flits (`req_o & gnt_i`). A downstream stall (`gnt_i` low while the winner still requests) just
///   pauses the burst. But if the winner *withdraws* its request mid-burst - including being masked
///   out by an upstream QoS/priority stage - the burst is **abandoned** and the arbiter re-arbitrates
///   to the next contender (`winner_gone`). This keeps the cell work-conserving and, crucially,
///   prevents a permanent stall when this cell is wrapped by a dynamic eligibility mask (see
///   `cc_qos_wrr_arbiter`). Under saturated traffic the winner never withdraws, so the bandwidth
///   ratio is exact; under non-saturation it degrades gracefully towards the offered load.
/// * **Weight of 0 means "no service".** An input whose weight is 0 is excluded from arbitration
///   entirely: it is skipped and never granted, even while it is requesting (it gets zero
///   bandwidth, as the weight says). This also keeps the burst counter from ever loading 0. If
///   *every* requesting input has weight 0, the output simply stays idle.
module cc_wrr_arbiter #(
  /// Number of request ports to arbitrate.
  parameter int unsigned NumIn     = 4,
  /// Data width of the payload in bits. Not needed if `data_t` is overwritten.
  parameter int unsigned DataWidth = 32,
  /// Data type of the payload, can be overwritten with a custom type.
  parameter type         data_t    = logic [DataWidth-1:0],
  /// Width of the per-input weight signal. A weight may range `[0, 2**WtWidth-1]`. A weight of 0
  /// excludes the input from arbitration (no service); otherwise the burst length is `weight` flits.
  parameter int unsigned WtWidth   = 4,
  /// Width of the arbitrated index.
  localparam int unsigned IdxWidth = cc_pkg::idx_width(NumIn),
  /// Type of the arbitrated index.
  localparam type         idx_t    = logic [IdxWidth-1:0]
) (
  input  logic                            clk_i,
  /// Asynchronous reset, active low.
  input  logic                            rst_ni,
  /// Synchronously clears the arbiter state (snapshot, counter, pointer).
  input  logic                            flush_i,
  /// Input request / valid, one per requester.
  input  logic    [NumIn-1:0]             req_i,
  /// Input grant / ready, one per requester.
  output logic    [NumIn-1:0]             gnt_o,
  /// Input data for each requester.
  input  data_t   [NumIn-1:0]             data_i,
  /// Per-input weight. The winner is granted `weights_i[winner]` consecutive flits; a weight of 0
  /// excludes that input from arbitration.
  input  logic    [NumIn-1:0][WtWidth-1:0] weights_i,
  /// Output request / valid.
  output logic                            req_o,
  /// Output grant / ready.
  input  logic                            gnt_i,
  /// Output data of the winning input.
  output data_t                           data_o,
  /// Index of the winning input.
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
