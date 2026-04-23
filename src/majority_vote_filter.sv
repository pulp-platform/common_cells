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
// The output q_o is high if at least THRESHOLD of 
// the last WINDOW_LEN samples are '1', otherwise low.
// New data is shifted in when enabled (en_i).
// clear_i synchronously resets the history and output to '0.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module majority_vote_filter #(
    parameter int unsigned WINDOW_LEN = 4,
    parameter int unsigned THRESHOLD  = (WINDOW_LEN / 2) + 1
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic clear_i,
    input  logic en_i,
    input  logic d_i,
    output logic q_o
);
    localparam int unsigned CNT_WIDTH = $clog2(WINDOW_LEN+1);

    logic [CNT_WIDTH-1:0] popcount_o;
    logic [WINDOW_LEN-1:0] history_d, history_q;

    assign history_d = {history_q[WINDOW_LEN-2:0], d_i};
    `FFLARNC(history_q, history_d, en_i, clear_i, '0, clk_i, rst_ni)

    popcount #(
        .INPUT_WIDTH(WINDOW_LEN)
    ) i_popcount (
        .data_i(history_q),
        .popcount_o(popcount_o)
    );

    assign q_o = (popcount_o >= CNT_WIDTH'(THRESHOLD));

`ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(WindowLenGeqZero, WINDOW_LEN >= 2, 
                "majority_vote_filter: WINDOW_LEN must be >= 2")
    `ASSERT_INIT(ThresholdGeqZero, THRESHOLD >= 1, 
                "majority_vote_filter: THRESHOLD must be >= 1")
    `ASSERT_INIT(ThresholdLeqWindowLen, THRESHOLD <= WINDOW_LEN, 
                "majority_vote_filter: THRESHOLD must be <= WINDOW_LEN")
`endif

endmodule
