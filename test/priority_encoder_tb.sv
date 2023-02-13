/*******************************************************************************
 * Copyright 2023 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 ******************************************************************************/
/*
 * Module `priority_encoder_tb`
 *
 * A testbench for the priority encoder module.
 *
 * It tests the priority encoder module in two configurations, with input
 * signal width of 5 and 8.
 *
 * Author: Emanuele Parisi <emanuele.parisi@unibo.it>
 */

module priority_encoder_tb ();

    localparam int unsigned DUT0_N_BITS = 8;
    localparam int unsigned DUT1_N_BITS = 5;

    logic [DUT0_N_BITS-1:0]         dut0_data_i;
    logic [$clog2(DUT0_N_BITS)-1:0] dut0_data_o;
    logic                           dut0_valid_o;

    logic [DUT1_N_BITS-1:0]         dut1_data_i;
    logic [$clog2(DUT1_N_BITS)-1:0] dut1_data_o;
    logic                           dut1_valid_o;

    priority_encoder #(.N_BITS(DUT0_N_BITS)) dut0 (
        .data_i (dut0_data_i),
        .data_o (dut0_data_o),
        .valid_o(dut0_valid_o)
    );

    priority_encoder #(.N_BITS(DUT1_N_BITS)) dut1 (
        .data_i (dut1_data_i),
        .data_o (dut1_data_o),
        .valid_o(dut1_valid_o)
    );

    initial begin
        // Apply test stimuli to DUT 0.
        dut1_data_i = 'b0;
        for (int i=0; i<2**DUT0_N_BITS; i++) begin
            dut0_data_i = i;
            #1;
        end

        // Apply test stimuli to DUT 1.
        dut0_data_i = 'b0;
        for (int i=0; i<2**DUT1_N_BITS; i++) begin
            dut1_data_i = i;
            #1;
        end

        $finish;
    end

endmodule
