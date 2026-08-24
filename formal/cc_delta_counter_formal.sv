// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Elaboration harness instantiating cc_delta_counter for every checked width
// and overflow mode.  delta_i remains unconstrained by the harness.
module cc_delta_counter_formal #(
    parameter int unsigned MaxWidth = 8
) (
    input logic [MaxWidth-1:0] delta_i,
    input logic [MaxWidth-1:0] d_i,
    input logic                 clk_i,
    input logic                 rst_ni,
    input logic                 clr_i,
    input logic                 en_i,
    input logic                 load_i,
    input logic                 down_i
);

    for (genvar width = 1; width <= MaxWidth; width++) begin : gen_width
        localparam int unsigned Width = width;

        for (genvar sticky = 0; sticky < 2; sticky++) begin : gen_sticky
            logic [Width-1:0] q;
            logic             overflow;

            cc_delta_counter #(
                .Width          ( Width         ),
                .StickyOverflow ( sticky != 0   )
            ) i_delta_counter (
                .clk_i      ( clk_i                      ),
                .rst_ni     ( rst_ni                     ),
                .clr_i      ( clr_i                      ),
                .en_i       ( en_i                       ),
                .load_i     ( load_i                     ),
                .down_i     ( down_i                     ),
                .delta_i    ( delta_i[Width-1:0]         ),
                .d_i        ( d_i[Width-1:0]             ),
                .q_o        ( q                          ),
                .overflow_o ( overflow                   )
            );

            cc_counter_properties #(
                .WIDTH                    ( Width       ),
                .STICKY_OVERFLOW          ( sticky != 0 ),
                .CHECK_COMMON_COVERS      ( Width == 1 && sticky == 0 ),
                .CHECK_ARITHMETIC_COVERS  ( sticky == 0 ),
                .CHECK_RESET_COVERS       ( Width == 1 && sticky == 0 )
            ) i_delta_counter_properties (
                .clk_i      ( clk_i                       ),
                .rst_ni     ( rst_ni                      ),
                .clr_i      ( clr_i                       ),
                .en_i       ( en_i                        ),
                .load_i     ( load_i                      ),
                .down_i     ( down_i                      ),
                .delta_i    ( delta_i[Width-1:0]          ),
                .d_i        ( d_i[Width-1:0]              ),
                .q_o        ( q                           ),
                .overflow_o ( overflow                    )
            );
        end
    end

endmodule : cc_delta_counter_formal
