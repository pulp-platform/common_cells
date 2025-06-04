// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>
//
// Counter which resets automatically when it reaches a specified bound, i.e.
// when it "trips". Useful e.g. for implementing hardware loop logic.

module trip_counter #(
    parameter int unsigned WIDTH = 4
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             en_i,
    input  logic [WIDTH-1:0] delta_i,
    input  logic [WIDTH-1:0] bound_i,
    output logic [WIDTH-1:0] q_o,
    output logic             last_o,
    output logic             trip_o
);

    delta_counter #(
        .WIDTH(WIDTH)
    ) i_delta_counter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .clear_i(trip_o),
        .en_i(en_i),
        .load_i(1'b0),
        .down_i(1'b0),
        .delta_i(delta_i),
        .d_i('0),
        .q_o(q_o),
        .overflow_o()
    );

    assign last_o = (q_o == bound_i);
    assign trip_o = last_o && en_i;

endmodule
