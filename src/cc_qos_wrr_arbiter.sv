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
// At design-time, each mechanism can be enabled or disabled (bypassed) through a dedicated
// parameter:
// * `EnableQos`: Enable the QoS priority-aware arbitration. If disabled, `qos_i` is ignored and all
//                inputs are at the same QoS priority level.
// * `EnableWeights`: Enable the weighted round-robin arbitration. If disabled, `weights_i` is
//                    ignored and all weights are 1, i.e., standard round-robin arbitration.
// * `EnableAging`: Enable QoS aging. Aging depends on QoS, so this parameter is only effective if
//                  `EnableQos` is set.
//
// At runtime, with all inputs at the same QoS priority level, the arbiter behaves like
// `cc_wrr_arbiter`. Moreover, if all weights are set to 1, the module behaves like a standard
// round-robin arbiter.

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
  // Number of output transfers after which the age of an input held back by QoS is incremented.
  parameter int unsigned AgingThreshold = 16,
  // Enable the QoS priority-aware arbitration.
  parameter bit          EnableQos      = 1'b1,
  // Enable the weighted round-robin arbitration.
  parameter bit          EnableWeights  = 1'b1,
  // Enable QoS aging. Only effective if `EnableQos` is set.
  parameter bit          EnableAging    = 1'b1,
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
  localparam int unsigned EffWidth      = QosWidth + 1,
  // Width of the aging counter, which counts up to `AgingThreshold` output transfers.
  localparam int unsigned AgingCntWidth = (AgingThreshold > 32'd1) ?
                                          unsigned'($clog2(AgingThreshold)) : 32'd1,
  // Aging is only active together with QoS.
  localparam bit          AgingActive   = EnableQos && EnableAging,
  // Width of the weights of the inner weighted arbiter. 1 bit if the weights are disabled.
  localparam int unsigned WrrWeightWidth = EnableWeights ? WeightWidth : 32'd1
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

  logic                      transfer;                     // one output transfer
  logic                      lock_q,        lock_d;        // output stalled: freeze `qos_req_d`
  logic [NumIn-1:0]          qos_req_q,     qos_req_d;     // contenders of the WRR arbiter

  logic [NumIn-1:0]          top_qos_req;                  // inputs at highest effective level
  logic [EffWidth-1:0]       eff_qos [NumIn];              // input QoS priority level + age
  logic [EffWidth-1:0]       max_eff_qos;                  // highest effective QoS priority level

  logic                      aging_qos_up;                 // upgrade QoS to avoid starvation
  logic [AgingCntWidth-1:0]  aging_cnt_q,   aging_cnt_d;   // transfers since last QoS upgrade
  logic [AgingWidth-1:0]     age_q [NumIn], age_d [NumIn]; // age of each input

  logic [NumIn-1:0][WrrWeightWidth-1:0] wrr_weights;       // weights of the WRR arbiter

  /////////////////////
  // Aging prescaler //
  /////////////////////
  assign transfer = req_o & gnt_i;

  if (AgingActive) begin : gen_aging_prescaler
    assign aging_qos_up = transfer & ((AgingThreshold <= 1) ? 1'b1 :
                          (aging_cnt_q == AgingCntWidth'(AgingThreshold - 1)));
    assign aging_cnt_d  = ~transfer ? aging_cnt_q : (aging_qos_up ? '0 : (aging_cnt_q + 1'b1));

    `FFARNC(aging_cnt_q, aging_cnt_d, flush_i, '0, clk_i, rst_ni)
  end else begin : gen_no_aging_prescaler
    assign aging_qos_up = 1'b0;
    assign aging_cnt_q  = '0;
    assign aging_cnt_d  = '0;
  end

  ////////////////////////
  // QoS priority level //
  ////////////////////////
  if (EnableQos) begin : gen_qos
    // Compute the effective QoS priority level by summing the input QoS priority level and the
    // age.
    for (genvar i = 0; i < NumIn; i++) begin : gen_eff_qos
      assign eff_qos[i] = EffWidth'(qos_i[i]) + EffWidth'(age_q[i]);
    end

    // Mask the requests that are not at the highest effective QoS priority level.
    always_comb begin : proc_top_qos_req
      max_eff_qos = '0;
      for (int unsigned i = 0; i < NumIn; i++) begin
        if (req_i[i] && (eff_qos[i] > max_eff_qos))
          max_eff_qos = eff_qos[i];
      end
      for (int unsigned i = 0; i < NumIn; i++) begin
        top_qos_req[i] = req_i[i] && (eff_qos[i] == max_eff_qos);
      end
    end

    // Freeze the contenders while the output is stalled, so that `req_o` is never withdrawn
    // because of a higher-priority request arriving in the meantime.
    assign lock_d    = req_o & ~gnt_i;
    assign qos_req_d = lock_q ? (qos_req_q & req_i) : top_qos_req;

    `FFARNC(lock_q,    lock_d,    flush_i, 1'b0, clk_i, rst_ni)
    `FFARNC(qos_req_q, qos_req_d, flush_i, '0,   clk_i, rst_ni)
  end else begin : gen_no_qos
    // All inputs are at the same QoS priority level.
    for (genvar i = 0; i < NumIn; i++) begin : gen_eff_qos
      assign eff_qos[i] = '0;
    end
    assign max_eff_qos = '0;
    assign top_qos_req = req_i;
    assign lock_d      = 1'b0;
    assign lock_q      = 1'b0;
    assign qos_req_d   = req_i;
    assign qos_req_q   = '0;
  end

  //////////////////////////
  // Weighted round-robin //
  //////////////////////////
  if (EnableWeights) begin : gen_weights
    assign wrr_weights = weights_i;
  end else begin : gen_no_weights
    // All weights are 1.
    for (genvar i = 0; i < NumIn; i++) begin : gen_unit_weights
      assign wrr_weights[i] = WrrWeightWidth'(1);
    end
  end

  cc_wrr_arbiter #(
    .NumIn       ( NumIn          ),
    .DataWidth   ( DataWidth      ),
    .data_t      ( data_t         ),
    .WeightWidth ( WrrWeightWidth )
  ) i_cc_wrr_arbiter (
    .clk_i,
    .rst_ni,
    .flush_i   ( flush_i     ),
    .req_i     ( qos_req_d   ),
    .gnt_o     ( gnt_o       ),
    .data_i    ( data_i      ),
    .weights_i ( wrr_weights ),
    .req_o     ( req_o       ),
    .gnt_i     ( gnt_i       ),
    .data_o    ( data_o      ),
    .idx_o     ( idx_o       )
  );

  //////////////////
  // Aging update //
  //////////////////
  if (AgingActive) begin : gen_aging
    always_comb begin : proc_age
      for (int unsigned i = 0; i < NumIn; i++) begin
        // Reset the age if the input is served or idle.
        if (gnt_o[i] || !req_i[i]) begin
          age_d[i] = '0;
        // Hold the age while the input is at the highest QoS priority level.
        end else if (top_qos_req[i]) begin
          age_d[i] = age_q[i];
        // Upgrade the QoS priority level when the aging threshold is reached, saturating at
        // `AgingQosMax`.
        end else if (aging_qos_up) begin
          age_d[i] = (age_q[i] == AgingWidth'(AgingQosMax)) ? age_q[i] : (age_q[i] + 1'b1);
        end else begin
          age_d[i] = age_q[i];
        end
      end
    end

    for (genvar i = 0; i < NumIn; i++) begin : gen_age_ff
      `FFARNC(age_q[i], age_d[i], flush_i, '0, clk_i, rst_ni)
    end
  end else begin : gen_no_aging
    // The ages stay 0: the effective QoS priority level is the input QoS priority level.
    for (genvar i = 0; i < NumIn; i++) begin : gen_age
      assign age_d[i] = '0;
      assign age_q[i] = '0;
    end
  end

  ////////////////
  // Assertions //
  ////////////////
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(numin_0, NumIn >= 1, "Need at least one input.")
  `ASSERT(req_implies_input, req_o |-> |req_i, clk_i, !rst_ni || flush_i,
          "Output valid must imply at least one input valid.")
  `ASSERT(req_stable, req_o && !gnt_i |=> req_o && (idx_o == $past(idx_o)), clk_i,
          !rst_ni || flush_i, "Output valid must stay stable until it is granted.")
  if (EnableQos) begin : gen_qos_assumptions
    for (genvar i = 0; i < NumIn; i++) begin : gen_qos_stable
      `ASSUME(qos_stable, req_i[i] && !gnt_o[i] |=> $stable(qos_i[i]), clk_i, !rst_ni || flush_i,
              $sformatf("QoS of input %0d changed while its request was waiting.", i))
    end
    `ASSERT(eff_qos_bounded, max_eff_qos <= EffWidth'(AgingQosMax), clk_i, !rst_ni || flush_i,
            "Effective QoS priority level above the highest QoS priority level.")
  end
  `ASSERT_INIT(aging_threshold_0, AgingThreshold >= 1, "AgingThreshold must be at least 1.")
  `endif

endmodule
