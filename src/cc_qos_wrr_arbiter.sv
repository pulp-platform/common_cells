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
// Description: Combined QoS-priority + weighted-round-robin arbiter.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

/// # QoS + Weighted-Round-Robin Arbiter (`cc_qos_wrr_arbiter`)
///
/// Combines the two arbitration axes into one cell:
/// * **`qos_i`** (priority / latency): higher QoS is served first. A waiting request's effective
///   QoS *ages* upward so it is never starved.
/// * **`weights_i`** (bandwidth): among the requesters that share the *winning* QoS tier, the
///   output bandwidth is split in proportion to their weights via `cc_wrr_arbiter`.
///
/// So QoS chooses *which tier* is served, and the weight chooses *how the tier's bandwidth is
/// divided*. Mechanism:
///
///   effective_qos[i] = qos_i[i] + age[i]
///   max_eff          = max over contenders of effective_qos[i]
///   eligible[i]      = req_i[i] && (effective_qos[i] == max_eff)   // the winning QoS tier
///   winner           = weighted round robin (by weights_i) among `eligible`   // cc_wrr_arbiter
///
/// For all i, `age[i]` climbs by 1 every `AgingInterval` number of transfered flits
/// while input `i` is requesting but *not* in the winning tier (i.e. held back due to low QoS);
/// the aging pauses once the input reaches the tier (where the weighted RR then guarantees its
/// turn) and resets to 0 when granted. Counting grants rather than absolute clock cycles helps
/// in preventing a downstream stall does not inflate the age[i].
///
/// ## Design notes
///   Reuse `cc_wrr_arbiter` for the within-tier split. That cell already snapshots its
///   contender set and locks the winner for the burst, so the (continuously recomputed) `eligible`
///   mask can be fed to it directly; it re-evaluates the tier at each burst boundary.
///
///   Weight 0 means no participation
///
///   Aging only the QoS-blocked inputs (not the ones merely awaiting their weighted-RR turn)
///   Aging is counted per grant, not per clock (the prescaler advances only when a flit is
///   transferred).Use a clock-cycle prescaler instead if a hard wall-clock latency bound is required.

module cc_qos_wrr_arbiter #(
  parameter int unsigned NumIn         = 4, /// Number of request ports to arbitrate.
  parameter int unsigned DataWidth     = 32, /// Payload width in bits. Unused if `data_t` is set.
  parameter type         data_t        = logic [DataWidth-1:0], /// Data type of the payload.
  parameter int unsigned QosWidth      = 4, /// Width of per-input QoS level (AXI AxQOS is 4 bits).
  parameter int unsigned WtWidth       = 4, /// Width of the per-input weight signal.
  parameter int unsigned AgeWidth      = 4, /// Width of the per-input aging counter.

  /// Number of grants (served flits) a QoS-blocked request waits per +1 of effective QoS.
  /// Counted in forward-progress cycles, not clock cycles, so stalls do not age requests. Must be >= 1.
  parameter int unsigned AgingInterval = 16,

  /// Dependent parameters, do not overwrite.
  localparam int unsigned IdxWidth     = cc_pkg::idx_width(NumIn),
  localparam type         idx_t        = logic [IdxWidth-1:0],
  localparam int unsigned EffWidth     = cc_pkg::max(QosWidth, AgeWidth) + 1
) (
  input  logic                            clk_i,
  input  logic                            rst_ni,
  input  logic                            flush_i,
  input  logic    [NumIn-1:0]             req_i,
  output logic    [NumIn-1:0]             gnt_o,
  input  data_t   [NumIn-1:0]             data_i,

  // Per-input QoS level (priority); higher is served first.
  input  logic    [NumIn-1:0][QosWidth-1:0] qos_i,
  // Per-input weight; splits a tier's bandwidth. A weight of 0 excludes the input.
  input  logic    [NumIn-1:0][WtWidth-1:0]  weights_i,

  output logic                            req_o,
  input  logic                            gnt_i,
  output data_t                           data_o,
  output idx_t                            idx_o
);

  // ---------------------------------------------------------------------------------------------
  // Aging prescaler: one tick every 'AgingInterval' grants (forward-progress cycles)
  // Aging therefore tracks how many served flits a request was passed over for, not
  // wall-clock time. The prescaler is frozen whenever the output is stalled (no flit transferred),
  // so a downstream stall neither inflates ages nor scrambles the QoS order when traffic resumes.
  // ---------------------------------------------------------------------------------------------
  localparam int unsigned GntCntWidth = (AgingInterval <= 1) ? 1 : $clog2(AgingInterval);
  logic [GntCntWidth-1:0] gnt_cnt_q, gnt_cnt_d; // for counting AgingInterval number of grants
  logic                tick;
  logic                flit_transfer;
  assign flit_transfer = req_o & gnt_i;  // a flit is actually granted (forward progress) this cycle
  // tick is high means AgingInterval number of grants have completed
  assign tick          = flit_transfer & ((AgingInterval <= 1) ? 1'b1 :
                         (gnt_cnt_q == GntCntWidth'(AgingInterval - 1)));
  assign gnt_cnt_d         = ~flit_transfer ? gnt_cnt_q : (tick ? '0 : (gnt_cnt_q + 1'b1));

  `FFARNC(gnt_cnt_q, gnt_cnt_d, flush_i, '0, clk_i, rst_ni)

  // ---------------------------------------------------------------------------------------------
  // Effective QoS = static QoS + age, and the winning-tier eligibility mask.
  // ---------------------------------------------------------------------------------------------
  logic [AgeWidth-1:0]  age_q   [NumIn], age_d [NumIn];
  logic [EffWidth-1:0]  eff_qos [NumIn];
  logic [EffWidth-1:0]  max_eff;
  logic [NumIn-1:0]     arb_req;   // requesting AND non-zero weight
  logic [NumIn-1:0]     eligible;

  for (genvar i = 0; i < NumIn; i++) begin : gen_eff
    assign eff_qos[i] = EffWidth'(qos_i[i]) + EffWidth'(age_q[i]);
  end

  // A weight-0 input gets no service, so its masked out

  always_comb begin : proc_arb_req
    for (int unsigned i = 0; i < NumIn; i++)
      arb_req[i] = req_i[i] & (weights_i[i] != '0);
  end

  always_comb begin : proc_tier
    max_eff = '0;
    for (int unsigned i = 0; i < NumIn; i++) begin
      if (arb_req[i] && (eff_qos[i] > max_eff))
        max_eff = eff_qos[i];
    end
    for (int unsigned i = 0; i < NumIn; i++) begin
      eligible[i] = arb_req[i] && (eff_qos[i] == max_eff);
    end
  end

  // ---------------------------------------------------------------------------------------------
  // Weighted round robin within the winning tier (reuse cc_wrr_arbiter, incl. its data mux).
  // The eligible mask may be fed directly: cc_wrr_arbiter snapshots/locks internally and
  // re-evaluates the tier at every burst boundary.
  // ---------------------------------------------------------------------------------------------
  cc_wrr_arbiter #(
    .NumIn     ( NumIn  ),
    .DataWidth ( DataWidth ),
    .data_t    ( data_t ),
    .WtWidth   ( WtWidth )
  ) i_cc_wrr_arbiter (
    .clk_i,
    .rst_ni,
    .flush_i   ( flush_i   ),
    .req_i     ( eligible  ),
    .gnt_o     ( gnt_o     ),
    .data_i    ( data_i    ),
    .weights_i ( weights_i ),
    .req_o     ( req_o     ),
    .gnt_i     ( gnt_i     ),
    .data_o    ( data_o    ),
    .idx_o     ( idx_o     )
  );

  // ---------------------------------------------------------------------------------------------
  // Aging update: reset on grant / when idle; climb only while QoS-blocked (requesting but not in
  // the winning tier); hold while in the winning tier (the weighted RR already guarantees a turn).
  // ---------------------------------------------------------------------------------------------
  always_comb begin : proc_age
    for (int unsigned i = 0; i < NumIn; i++) begin
      if (gnt_o[i] || !arb_req[i]) begin
        age_d[i] = '0;                       // served, idle, or weight 0
      end else if (eligible[i]) begin
        age_d[i] = age_q[i];                 // in winning tier, no need to age
      end else if (tick) begin
        // QoS-blocked -> age, saturating once the counter is already at its max
        age_d[i] = (age_q[i] == '1) ? age_q[i] : (age_q[i] + 1'b1);
      end else begin
        age_d[i] = age_q[i];
      end
    end
  end

  for (genvar i = 0; i < NumIn; i++) begin : gen_age_ff
    `FFARNC(age_q[i], age_d[i], flush_i, '0, clk_i, rst_ni)
  end

  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(numin_0, NumIn >= 1, "Need at least one input.")
  `ASSERT_INIT(aging_iv, AgingInterval >= 1, "AgingInterval must be at least 1.")
  `ASSERT(req_implies_input, req_o |-> |req_i, clk_i, !rst_ni || flush_i,
          "Output valid must imply at least one input valid.")
  `endif

endmodule
