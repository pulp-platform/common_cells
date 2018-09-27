// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: This module is a reset synchronizer with a dedicated reset bypass pin for testmode reset.

module rstgen_bypass (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic rst_test_mode_ni,
    input  logic test_mode_i,
    output logic rst_no,
    output logic init_no
);

    logic s_rst_ff3,s_rst_ff2,s_rst_ff1,s_rst_ff0,s_rst_n;

    always @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            s_rst_ff0  <= 1'b0;
            s_rst_ff1  <= 1'b0;
            s_rst_ff2  <= 1'b0;
            s_rst_ff3  <= 1'b0;
            s_rst_n    <= 1'b0;
        end else begin
            s_rst_ff3  <= 1'b1;
            s_rst_ff2  <= s_rst_ff3;
            s_rst_ff1  <= s_rst_ff2;
            s_rst_ff0  <= s_rst_ff1;
            s_rst_n    <= s_rst_ff0;
        end
    end

    // bypass mode
    always_comb begin
        if (test_mode_i == 1'b0) begin
            rst_no  = s_rst_n;
            init_no = s_rst_n;
        end else begin
            rst_no  = rst_test_mode_ni;
            init_no = 1'b1;
        end
    end

endmodule