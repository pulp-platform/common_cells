// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module mv_filter #(
    parameter int unsigned WIDTH     = 4,
    parameter int unsigned THRESHOLD = 10
)(
    input  logic clk_i,
    input  logic rst_ni,
    input  logic sample_i,
    input  logic clr_i,
    input  logic d_i,
    output logic q_o
);
    logic [WIDTH-1:0] counter_q, counter_d;
    logic d, q;

    assign q_o = q;

    always_comb begin
        counter_d = counter_q;
        d = q;

        if (counter_q >= THRESHOLD[WIDTH-1:0]) begin
            d = 1'b1;
        end else if (sample_i && d_i) begin
            counter_d = counter_q + 1;
        end
    end

    `FFARNC(counter_q, counter_d, clr_i, '0, clk_i, rst_ni)
    `FFARNC(q, d, clr_i, 1'b0, clk_i, rst_ni)
endmodule
