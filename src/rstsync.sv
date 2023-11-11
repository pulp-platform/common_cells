// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Nils Wistoff <nwistoff@iis.ee.ethz.ch>

module rstsync #(
    parameter int unsigned NumRegs = 4
) (
    input  logic clk_i,
    input  logic rst_ni,
    output logic rst_no
);
    logic [NumRegs-1:0] synch_regs_q;

    assign rst_no = synch_regs_q[NumRegs-1];

    always @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
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
