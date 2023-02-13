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
 * Module `priority_encoder`
 *
 * This module implements a fully-combinational priority encoder. 
 *
 * It takes as input a signal of `N_BITS` bits and returns the index of the 
 * first LSB set to 1. Any `N_BITS` value bigger than 1 is legal. The module 
 * pads the input signal internally to the next power of two, because of how
 * the recursive module instantiation work. The output signal width is 
 * $clog2(N_BITS) bits wide.
 *
 * Author: Emanuele Parisi <emanuele.parisi@unibo.it>
 */

module priority_encoder #(
    parameter int unsigned N_BITS = 8
) (
    input  logic [N_BITS-1:0]         data_i,
    output logic [$clog2(N_BITS)-1:0] data_o,
    output logic                      valid_o
);

    localparam int unsigned PADDED_N_BITS = 1 << $clog2(N_BITS);

    if (PADDED_N_BITS == 2) begin
        always_comb begin
            unique case (data_i) 
                2'b01, 2'b11: begin
                    data_o  = 'b0;
                    valid_o = 'b1;
                end
                2'b10: begin
                    data_o  = 'b1;
                    valid_o = 'b1;
                end
                default: begin
                    data_o  = 'b0;
                    valid_o = 'b0;
                end
            endcase
        end
    end else begin
        logic [PADDED_N_BITS-1:0]         padded_data;
        logic [$clog2(PADDED_N_BITS)-2:0] lsb_data;
        logic                             lsb_valid;
        logic [$clog2(PADDED_N_BITS)-2:0] msb_data;
        logic                             msb_valid;

        assign padded_data = data_i;

        priority_encoder #(.N_BITS(PADDED_N_BITS/2)) priority_encoder_lsb (
            .data_i  (padded_data[PADDED_N_BITS/2-1:0]),
            .data_o  (lsb_data),
            .valid_o (lsb_valid)
        );
        priority_encoder #(.N_BITS(PADDED_N_BITS/2)) priority_encoder_msb (
            .data_i  (padded_data[PADDED_N_BITS-1:PADDED_N_BITS/2]),
            .data_o  (msb_data),
            .valid_o (msb_valid)
        );

        always_comb begin
            unique case ({msb_valid, lsb_valid})
                2'b01, 2'b11: begin
                    data_o  = {1'b0, lsb_data};
                    valid_o = 'b1;
                end
                2'b10: begin
                    data_o  = {1'b1, msb_data};
                    valid_o = 'b1;
                end
                default: begin
                    data_o  = 'b0;
                    valid_o = 'b0;
                end
            endcase
        end
    end

endmodule
