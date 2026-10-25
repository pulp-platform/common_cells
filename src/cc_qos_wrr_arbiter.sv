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
// Description: QoS-aware weighted round-robin arbiter.
//
// This module extends standard round-robin arbitration with the three mechanisms described
// below.
//
// ## QoS priority-aware arbitration
//
// This mechanism arbitrates based on the QoS priority level of each input (`qos_i`). Traffic
// streams with a higher QoS priority level are served first. The output follows the valid/ready
// handshake. To this end, the set of inputs at the highest QoS priority level is frozen while
// the output is stalled, so that a higher-priority request arriving during a stall is only
// considered after the pending transfer.
//
// ## Weighted round-robin arbitration
//
// This mechanism distributes the bandwidth of the output channel shared by the `NumIn` inputs
// according to their weights (`weights_i`). The weight of an input determines the bandwidth share
// it is allocated whenever it wins arbitration. The higher the weight, the more bandwidth the
// input is granted on the shared output channel. Every weight must be at least 1. Further details
// can be found in the description of `cc_wrr_arbiter`.
//
// ## QoS aging
//
// This mechanism prevents the starvation of low-priority traffic streams, which could otherwise be
// preempted by high-priority streams indefinitely, and thus keep their input channel buffers
// occupied for a long time. The age of each input (`age[i]`) is added to its QoS priority level
// (`qos_i[i]`) to compute the effective QoS priority level (`eff_qos[i]`) used for arbitration.
// While an input is held back by inputs at a higher QoS priority level, its age is incremented by
// 1 every `AgingThreshold` valid/ready handshakes on the output. A handshake is generic and can
// represent a variety of transfers, such as a NoC packet or an AXI4 burst. The age stops growing
// once the input reaches the highest QoS priority level, where round-robin guarantees its turn,
// and is reset to 0 when the input is served. An input can gain up to `AgingQosMax` levels through
// aging, which spans the full QoS range: a request at the lowest QoS priority level can always age
// up to the highest one, so no input is ever starved.
//
// ## Modularity
//
// At design-time, each mechanism can be enabled or disabled through a dedicated parameter. When a
// mechanism is disabled, its functionality is completely bypassed. At runtime, with all inputs at
// the same QoS priority level, the arbiter behaves like `cc_wrr_arbiter`. Moreover, if all weights
// are set to 1, the module behaves cycle by cycle like a standard round-robin arbiter.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module cc_qos_wrr_arbiter #(
  // Number of request channels to arbitrate.
  parameter int unsigned NumIn          = 4,
  // Data width of the payload in bits. Not needed if `data_t` is overwritten.
  parameter int unsigned DataWidth      = 32,
  // Data type of the payload. It can be overwritten with a custom type.
  parameter type         data_t         = logic [DataWidth-1:0],
  // Width of the input QoS priority level. Default is 4.
  parameter int unsigned QosWidth       = 4,
  // Width of the input weights. A weight may range from 1 to `2**WeightWidth-1`.
  // A weight of 0 is illegal.
  parameter int unsigned WeightWidth    = 4,
  // Number of output transfers after which the age of a stalled input is incremented.
  parameter int unsigned AgingThreshold = 16,
  // Derived parameters, do **not** overwrite!
  //
  // Width of the arbitrated index.
  localparam int unsigned IdxWidth      = cc_pkg::idx_width(NumIn),
  // Type of the arbitrated index.
  localparam type         idx_t         = logic [IdxWidth-1:0],
  // Maximum number of QoS priority levels an input can gain through aging. It spans the full QoS
  // range, so that the lowest QoS priority level can age up to the highest one.
  localparam int unsigned AgingQosMax   = 2**QosWidth - 1,
  // Width of the age counter, which saturates at `AgingQosMax`.
  localparam int unsigned AgingWidth    = unsigned'($clog2(AgingQosMax + 1)),
  // Width of the effective QoS priority level (input QoS priority level + age).
  localparam int unsigned EffWidth      = QosWidth + 1
) (
  input  logic                               clk_i,
  input  logic                               rst_ni,
  input  logic                               flush_i,
  // Input channels.
  input  logic    [NumIn-1:0]                req_i,
  output logic    [NumIn-1:0]                gnt_o,
  input  data_t   [NumIn-1:0]                data_i,
  // Input QoS priority levels.
  input  logic    [NumIn-1:0][QosWidth-1:0]    qos_i,
  // Input weights.
  input  logic    [NumIn-1:0][WeightWidth-1:0] weights_i,
  // Output channel.
  output logic                               req_o,
  input  logic                               gnt_i,
  output data_t                              data_o,
  // Index from which input the data came from.
  output idx_t                               idx_o
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
