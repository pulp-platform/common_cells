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
// Description: Serial Line Deglitcher
// Update output only after d_i has remained stable for THRESHOLD cycles.
// The output q_o changes to the current level of d_i only after
// d_i has remained stable at that level for at least
// THRESHOLD consecutive enabled (en_i) clock cycles.
// clear_i synchronously resets the history and immediately sets q_o to current d_i.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module serial_deglitch #(
    parameter int unsigned THRESHOLD = 4
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic clear_i,
    input  logic en_i,
    input  logic d_i,
    output logic q_o
);
    localparam int unsigned CNT_WIDTH = cf_math_pkg::idx_width(THRESHOLD + 1);

    logic [CNT_WIDTH-1:0] count_q, count_d;
    logic                 mismatch, stable_edge;
    logic                 count_load, count_clear;
    logic                 q_d;

    assign mismatch = (d_i != q_o);
    assign count_d  = count_q + CNT_WIDTH'(1);

    // Update when the mismatch counter reaches THRESHOLD
    assign stable_edge = en_i && mismatch && (count_d == CNT_WIDTH'(THRESHOLD));
    // Clear if signal is not different/stable or when updating the output
    assign count_clear = clear_i || (en_i && !mismatch) || stable_edge;
    assign count_load  = en_i && mismatch && !stable_edge;

    assign q_d = (clear_i || stable_edge) ? d_i : q_o;

    `FFLARNC(count_q, count_d, count_load, count_clear, '0,  clk_i, rst_ni)
    `FF(q_o, q_d, 1'b0, clk_i, rst_ni)

`ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(ThresholdGtZero, THRESHOLD >= 1, "serial_deglitch: THRESHOLD must be >= 1")
`endif

endmodule