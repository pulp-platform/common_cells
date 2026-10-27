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
// according to their weights (`weight_i`). The weight of an input determines the bandwidth share
// it is allocated whenever it wins arbitration. The higher the weight, the more bandwidth the
// input is granted on the shared output channel. Every weight must be at least 1. Further details
// can be found in the description of `cc_wrr_arbiter`.
//
// ## QoS aging
//
// This mechanism prevents the starvation of low-priority traffic streams, which could otherwise be
// preempted by high-priority streams indefinitely, and thus keep their input channel buffers
// occupied for a long time. The QoS age of each input (`qos_aging[i]`), i.e., the QoS priority
// levels it gained through aging, is added to its QoS priority level (`qos_i[i]`) to compute the
// effective QoS priority level (`qos_eff[i]`) used for arbitration. While an input is held back by
// inputs at a higher QoS priority level, its QoS age is incremented by 1 every `AgingThreshold`
// valid/ready handshakes on the output. A handshake is generic and can represent a variety of
// transfers, such as a NoC packet or an AXI4 burst. Aging stops once the input reaches the highest
// QoS priority level, where round-robin guarantees its turn, and its QoS age is reset to 0 when the
// input is served. The QoS age can reach `AgingQosMax`, which spans the full QoS range: a request
// at the lowest QoS priority level can always age up to the highest one, so no input is ever
// starved.
//
// ## Modularity
//
// At design-time, each mechanism can be enabled or disabled (bypassed) through a dedicated
// parameter:
// * `EnableQos`: Enable the QoS priority-aware arbitration. If disabled, `qos_i` is ignored and all
//                inputs are at the same QoS priority level.
// * `EnableWrr`: Enable the weighted round-robin arbitration. If disabled, `weight_i` is ignored
//                and all weights are 1, i.e., standard round-robin arbitration.
// * `EnableAging`: Enable QoS aging. Aging depends on QoS, so this parameter is only effective if
//                  `EnableQos` is set.
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
  // Number of output transfers after which an input held back by QoS gains one QoS priority level
  // through aging.
  parameter int unsigned AgingThreshold = 16,
  // Enable the QoS priority-aware arbitration.
  parameter bit          EnableQos      = 1'b1,
  // Enable the weighted round-robin arbitration.
  parameter bit          EnableWrr      = 1'b1,
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
  // Width of the QoS age counter, which saturates at `AgingQosMax`.
  localparam int unsigned AgingWidth    = unsigned'($clog2(AgingQosMax + 1)),
  // Width of the effective QoS priority level (input QoS priority level + QoS age).
  localparam int unsigned EffWidth      = QosWidth + 1,
  // Width of the aging transfer counter (`qos_aging_cnt`), which counts up to `AgingThreshold`
  // output transfers.
  localparam int unsigned AgingCntWidth = (AgingThreshold > 32'd1) ?
                                          unsigned'($clog2(AgingThreshold)) : 32'd1,
  // Aging is only active together with QoS.
  localparam bit          AgingActive   = EnableQos && EnableAging,
  // Width of the weights of the inner weighted arbiter. 1 bit if the weights are disabled.
  localparam int unsigned WrrWeightWidth = EnableWrr ? WeightWidth : 32'd1
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
  input  logic    [NumIn-1:0][WeightWidth-1:0] weight_i,
  // Output channel.
  output logic                               req_o,
  input  logic                               gnt_i,
  output data_t                              data_o,
  // Index from which input the data came from.
  output idx_t                               idx_o,
  // Error flags for illegal weight values.
  output logic    [NumIn-1:0]                weight_error_o
);

  logic                      transfer;                     // one output transfer
  logic                      lock_q,        lock_d;        // output stalled: freeze `qos_req_d`
  logic [NumIn-1:0]          qos_req_q,     qos_req_d;     // contenders of the WRR arbiter

  // QoS prioritization.
  logic [NumIn-1:0]          qos_top_req;                  // inputs at highest effective level
  logic [EffWidth-1:0]       qos_eff [NumIn];              // input QoS priority level + QoS age
  logic [EffWidth-1:0]       qos_eff_max;                  // highest effective QoS priority level

  // QoS aging.
  logic [AgingWidth-1:0]     qos_aging [NumIn];            // QoS levels gained through aging
  logic [NumIn-1:0]          qos_aging_clr;                // clear the QoS age of each input
  logic [NumIn-1:0]          qos_aging_en;                 // increment the QoS age of each input
  logic                      qos_aging_up;                 // upgrade QoS to avoid starvation
  logic [AgingCntWidth-1:0]  qos_aging_cnt;                // transfers since last QoS upgrade

  // Weighted arbitration.
  logic [NumIn-1:0][WrrWeightWidth-1:0] qos_wrr_weight;    // weights of the WRR arbiter
  logic [NumIn-1:0]          qos_wrr_weight_error;         // weight errors of the WRR arbiter

  /////////////////////
  // Aging prescaler //
  /////////////////////
  assign transfer = req_o & gnt_i;

  if (AgingActive) begin : gen_aging_prescaler
    // Count the output transfers and restart after `AgingThreshold` of them.
    assign qos_aging_up = transfer & (qos_aging_cnt == AgingCntWidth'(AgingThreshold - 1));

    cc_counter #(
      .Width ( AgingCntWidth )
    ) i_qos_aging_cnt (
      .clk_i,
      .rst_ni,
      .clear_i    ( flush_i | qos_aging_up ),
      .en_i       ( transfer               ),
      .load_i     ( 1'b0                   ),
      .down_i     ( 1'b0                   ),
      .d_i        ( '0                     ),
      .q_o        ( qos_aging_cnt          ),
      .overflow_o ( /* unused */           )
    );
  end else begin : gen_no_aging_prescaler
    assign qos_aging_up  = 1'b0;
    assign qos_aging_cnt = '0;
  end

  ////////////////////////
  // QoS priority level //
  ////////////////////////
  if (EnableQos) begin : gen_qos
    // Calculate the effective QoS priority level from the input QoS and the QoS age.
    for (genvar i = 0; i < NumIn; i++) begin : gen_qos_eff
      assign qos_eff[i] = EffWidth'(qos_i[i]) + EffWidth'(qos_aging[i]);
    end

    // Mask the requests that are not at the highest effective QoS priority level.
    always_comb begin : proc_qos_top_req
      qos_eff_max = '0;
      for (int unsigned i = 0; i < NumIn; i++) begin
        if (req_i[i] && (qos_eff[i] > qos_eff_max))
          qos_eff_max = qos_eff[i];
      end
      for (int unsigned i = 0; i < NumIn; i++) begin
        qos_top_req[i] = req_i[i] && (qos_eff[i] == qos_eff_max);
      end
    end

    // Freeze the contenders while the output is stalled, so that `req_o` is never withdrawn
    // because of a higher-priority request arriving in the meantime.
    assign lock_d    = req_o & ~gnt_i;
    assign qos_req_d = lock_q ? (qos_req_q & req_i) : qos_top_req;

    `FFARNC(lock_q,    lock_d,    flush_i, 1'b0, clk_i, rst_ni)
    `FFARNC(qos_req_q, qos_req_d, flush_i, '0,   clk_i, rst_ni)
  end else begin : gen_no_qos
    // All inputs are at the same QoS priority level.
    for (genvar i = 0; i < NumIn; i++) begin : gen_qos_eff
      assign qos_eff[i] = '0;
    end
    assign qos_eff_max = '0;
    assign qos_top_req = req_i;
    assign lock_d      = 1'b0;
    assign lock_q      = 1'b0;
    assign qos_req_d   = req_i;
    assign qos_req_q   = '0;
  end

  //////////////////////////
  // Weighted round-robin //
  //////////////////////////
  if (EnableWrr) begin : gen_wrr
    assign qos_wrr_weight = weight_i;
  end else begin : gen_no_wrr
    // All weights are 1.
    for (genvar i = 0; i < NumIn; i++) begin : gen_unit_weights
      assign qos_wrr_weight[i] = WrrWeightWidth'(1);
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
    .flush_i        ( flush_i              ),
    .req_i          ( qos_req_d            ),
    .gnt_o          ( gnt_o                ),
    .data_i         ( data_i               ),
    .weight_i       ( qos_wrr_weight       ),
    .req_o          ( req_o                ),
    .gnt_i          ( gnt_i                ),
    .data_o         ( data_o               ),
    .idx_o          ( idx_o                ),
    .weight_error_o ( qos_wrr_weight_error )
  );

  assign weight_error_o = EnableWrr ? qos_wrr_weight_error : '0;

  //////////////////
  // Aging update //
  //////////////////
  if (AgingActive) begin : gen_aging
    for (genvar i = 0; i < NumIn; i++) begin : gen_qos_aging
      // Clear the QoS age if the input is served or idle.
      assign qos_aging_clr[i] = gnt_o[i] | ~req_i[i];
      // Upgrade the QoS priority level when the aging threshold is reached, unless the input is
      // at the highest QoS priority level. The QoS age saturates at `AgingQosMax`.
      assign qos_aging_en[i] = qos_aging_up & ~qos_top_req[i] &
                               (qos_aging[i] != AgingWidth'(AgingQosMax));

      cc_counter #(
        .Width ( AgingWidth )
      ) i_qos_aging (
        .clk_i,
        .rst_ni,
        .clear_i    ( flush_i | qos_aging_clr[i] ),
        .en_i       ( qos_aging_en[i]            ),
        .load_i     ( 1'b0                       ),
        .down_i     ( 1'b0                       ),
        .d_i        ( '0                         ),
        .q_o        ( qos_aging[i]               ),
        .overflow_o ( /* unused */               )
      );
    end
  end else begin : gen_no_aging
    // The QoS age stays 0.
    for (genvar i = 0; i < NumIn; i++) begin : gen_qos_aging
      assign qos_aging[i] = '0;
    end
    assign qos_aging_clr = '0;
    assign qos_aging_en  = '0;
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
    `ASSERT(qos_eff_bounded, qos_eff_max <= EffWidth'(AgingQosMax), clk_i, !rst_ni || flush_i,
            "Effective QoS priority level above the highest QoS priority level.")
  end
  `ASSERT_INIT(aging_threshold_0, AgingThreshold >= 1, "AgingThreshold must be at least 1.")
  `endif

endmodule
