// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Up/down counter that tracks its maximum value

`include "common_cells/registers.svh"

module cc_max_counter #(
    parameter int unsigned Width = 4
) (
    input  logic             clk_i,     // Clock
    input  logic             rst_ni,    // Asynchronous reset active low
    input  logic             clr_i,     // Synchronous clear active high
    input  logic             clr_cnt_i, // Synchronous clear for counter only
    input  logic             clr_max_i, // Synchronous clear for maximum value only
    input  logic             en_i,      // Enable the counter
    input  logic             load_i,    // Load a new value
    input  logic             down_i,    // Downcount, default is up
    input  logic [Width-1:0] delta_i,   // Counter delta
    input  logic [Width-1:0] d_i,
    output logic [Width-1:0] q_o,
    output logic [Width-1:0] max_o,
    output logic             overflow_o,
    output logic             overflow_max_o
);
    logic [Width-1:0] max_d, max_q;
    logic overflow_max_d, overflow_max_q;

    cc_delta_counter #(
        .Width          (Width),
        .StickyOverflow (1'b1)
    ) i_counter (
        .clk_i,
        .rst_ni,
        .clr_i(clr_i | clr_cnt_i),
        .en_i,
        .load_i,
        .down_i,
        .delta_i,
        .d_i,
        .q_o,
        .overflow_o
    );

    always_comb begin
        max_d = max_q;
        max_o = max_q;
        overflow_max_d = overflow_max_q;
        if (clr_max_i) begin
            max_d = '0;
            overflow_max_d = 1'b0;
        end else if (q_o > max_q) begin
            max_d = q_o;
            max_o = q_o;
            if (overflow_o) begin
                overflow_max_d = 1'b1;
            end
        end
    end

    assign overflow_max_o = overflow_max_q;

    `FFARNC(max_q, max_d, clr_i, '0, clk_i, rst_ni)
    `FFARNC(overflow_max_q, overflow_max_d, clr_i, 1'b0, clk_i, rst_ni)

endmodule
