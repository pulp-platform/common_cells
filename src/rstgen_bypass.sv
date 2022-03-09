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
// Pro Tip: The wise Dr. Schaffner recommends at least 4 registers!

module rstgen_bypass #(
    parameter int unsigned NumRegs = 4
) (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic rst_test_mode_ni,
    input  logic test_mode_i,
    output logic rst_no,
    output logic init_no
);

    // internal reset
    logic rst_n;

    logic [NumRegs-1:0] synch_regs_q;

    // bypass mode: use glitch-free (clock) multiplexers
    tc_clk_mux2 i_tc_clk_mux2_rst_n (
        .clk0_i     ( rst_ni ),
        .clk1_i     ( rst_test_mode_ni ),
        .clk_sel_i  ( test_mode_i ),
        .clk_o      ( rst_n )
    );

    tc_clk_mux2 i_tc_clk_mux2_rst_no (
        .clk0_i     ( synch_regs_q[NumRegs-1] ),
        .clk1_i     ( rst_test_mode_ni ),
        .clk_sel_i  ( test_mode_i ),
        .clk_o      ( rst_no )
    );

    tc_clk_mux2 i_tc_clk_mux2_init_no (
        .clk0_i     ( synch_regs_q[NumRegs-1] ),
        .clk1_i     ( 1'b1 ),
        .clk_sel_i  ( test_mode_i ),
        .clk_o      ( init_no )
    );

    always @(posedge clk_i or negedge rst_n) begin
        if (~rst_n) begin
            synch_regs_q <= 0;
        end else begin
            synch_regs_q <= {synch_regs_q[NumRegs-2:0], 1'b1};
        end
    end
    // pragma translate_off
    `ifndef VERILATOR
    initial begin : p_assertions
        if (NumRegs < 1) $fatal(1, "At least one register is required.");
    end
    `endif
    // pragma translate_on
endmodule
