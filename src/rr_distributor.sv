// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Thomas Benz <tbenz@iis.ee.ethz.ch>, ETH Zurich
// Date: 12.01.2021
// Description: round robin distributor

/// The rr_distributor forwards requests to individual outputs in a round robin fashion.
module rr_distributor # (
    /// Number of outputs to distribute to.
    parameter int unsigned NumOut    = 1,
    /// Data width of the payload in bits. Not needed if `payload_t` is overwritten.
    parameter int unsigned Width     = 1,
    /// Data type of the payload, can be overwritten with a custom type. Only use of `Width`.
    parameter type         payload_t = logic [Width-1:0],
    /// Dependent parameter, do **not** overwrite.
    /// Width of the selected index
    parameter int unsigned IdxWidth  = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1,
    /// Dependent parameter, do **not** overwrite.
    /// type of the selected index
    parameter type         idx_t     = logic [IdxWidth-1:0]
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,
    // input stream
    input  logic                  valid_i,
    output logic                  ready_o,
    input  payload_t              payload_i,
    // output stream
    output logic     [NumOut-1:0] valid_o,
    input  logic     [NumOut-1:0] ready_i,
    output payload_t [NumOut-1:0] payload_o,
    output idx_t                  sel_o
);

    if (NumOut == 1) begin : gen_bypass
        assign valid_o[0] = valid_i;
        assign ready_o    = ready_i[0];
        assign sel_o      = 1'b0;
    end else begin : gen_arb

        idx_t rr_d, rr_q;
        logic one_ready;

        assign rr_d = (valid_i & one_ready) ?
            ((rr_q == idx_t'(NumOut-1)) ? '0 : rr_q + 1'b1) : rr_q;

        assign one_ready = |ready_i;

        always_comb begin : proc_arbitration
            valid_o = '0;
            ready_o = 1'b0;
            if (ready_i[rr_q]) begin
                valid_o[rr_q] = valid_i;
                ready_o = 1'b1;
            end
        end

        always_ff @(posedge clk_i or negedge rst_ni) begin : proc_prio_regs
            if(~rst_ni) begin
                rr_q <= 0;
            end else begin
                rr_q <= rr_d;
            end
        end

        assign sel_o = rr_q;
    end

    assign payload_o = {{NumOut}{payload_i}};

endmodule : rr_distributor
