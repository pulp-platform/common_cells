// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Up/down counter with variable delta

`include "common_cells/registers.svh"

module cc_delta_counter #(
    parameter int unsigned Width = 4,
    parameter bit StickyOverflow = 1'b0
)(
    input  logic             clk_i,   // Clock
    input  logic             rst_ni,  // Asynchronous reset active low
    input  logic             clr_i,   // Synchronous clear active high
    input  logic             en_i,    // Enable the counter
    input  logic             load_i,  // Load a new value
    input  logic             down_i,  // Downcount, default is up
    input  logic [Width-1:0] delta_i,
    input  logic [Width-1:0] d_i,
    output logic [Width-1:0] q_o,
    output logic             overflow_o
);
    logic [Width:0] counter_q, counter_d;
    if (StickyOverflow) begin : gen_sticky_overflow
        logic overflow_d, overflow_q;
        logic overflow_clr;

        assign overflow_clr = clr_i || load_i;
        `FFARNC(overflow_q, overflow_d, overflow_clr, 1'b0, clk_i, rst_ni)

        always_comb begin
            overflow_d = overflow_q;
            if (!overflow_q && en_i) begin
                if (down_i) begin
                    overflow_d = delta_i > counter_q[Width-1:0];
                end else begin
                    overflow_d = counter_q[Width-1:0] > ({Width{1'b1}} - delta_i);
                end
            end
        end
        assign overflow_o = overflow_q;
    end else begin : gen_transient_overflow
        // counter overflowed if the MSB is set
        assign overflow_o = counter_q[Width];
    end
    assign q_o = counter_q[Width-1:0];

    always_comb begin
        counter_d = counter_q;

        if (load_i) begin
            counter_d = {1'b0, d_i};
        end else if (en_i) begin
            if (down_i) begin
                counter_d = counter_q - delta_i;
            end else begin
                counter_d = counter_q + delta_i;
            end
        end
    end

    `FFARNC(counter_q, counter_d, clr_i, '0, clk_i, rst_ni)
endmodule
