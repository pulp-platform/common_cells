// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Philippe Sauter <phsauter@iis.ee.ethz.ch>
//
// Description: Majority-Vote Filter
// Smooth noisy data using a moving window threshold vote.
// The output q_o is high if at least Threshold of
// the last WindowLen samples are '1', otherwise low.
// New data is shifted in when enabled (en_i).
// clr_i synchronously resets the history and output to '0.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module cc_majority_vote_filter #(
    parameter int unsigned WindowLen = 4,
    parameter int unsigned Threshold  = (WindowLen / 2) + 1
)(
    input  logic clk_i,  // Clock
    input  logic rst_ni, // Asynchronous reset active low
    input  logic clr_i,  // Synchronous clear active high
    input  logic en_i,
    input  logic d_i,
    output logic q_o
);
    localparam int unsigned CntWidth = $clog2(WindowLen+1);

    logic [CntWidth-1:0]  popcount_o;
    logic [WindowLen-1:0] history_d, history_q;

    assign history_d = {history_q[WindowLen-2:0], d_i};
    `FFLARNC(history_q, history_d, en_i, clr_i, '0, clk_i, rst_ni)

    cc_popcount #(
        .InputWidth(WindowLen)
    ) i_popcount (
        .data_i(history_q),
        .popcount_o(popcount_o)
    );

    assign q_o = (popcount_o >= CntWidth'(Threshold));

`ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(WindowLenGeqZero, WindowLen >= 2,
                "cc_majority_vote_filter: WindowLen must be >= 2")
    `ASSERT_INIT(ThresholdGeqZero, Threshold >= 1,
                "cc_majority_vote_filter: Threshold must be >= 1")
    `ASSERT_INIT(ThresholdLeqWindowLen, Threshold <= WindowLen,
                "cc_majority_vote_filter: Threshold must be <= WindowLen")
`endif

endmodule
