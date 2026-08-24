// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software and hardware distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Elaboration harness for one- and four-bit payloads.
module cc_fall_through_register_formal (
    input logic            clk_i,
    input logic            rst_ni,
    input logic [1:0]      clr_i,
    input logic [1:0]      valid_i,
    input logic [1:0]      ready_i,
    input logic [1:0][3:0] data_i
);

    for (genvar width_idx = 0; width_idx < 2; width_idx++) begin : gen_width
        localparam int unsigned DataWidth = (width_idx == 0) ? 1 : 4;
        localparam int unsigned Index = width_idx;
        typedef logic [DataWidth-1:0] payload_t;

        logic ready_o;
        logic valid_o;
        logic [DataWidth-1:0] data_o;

        cc_fall_through_register #(
            .data_t ( payload_t )
        ) i_fall_through_register (
            .clk_i   ( clk_i             ),
            .rst_ni  ( rst_ni            ),
            .clr_i   ( clr_i[Index]      ),
            .valid_i ( valid_i[Index]    ),
            .ready_o ( ready_o           ),
            .data_i  ( data_i[Index][DataWidth-1:0] ),
            .valid_o ( valid_o           ),
            .ready_i ( ready_i[Index]    ),
            .data_o  ( data_o            )
        );

        cc_fall_through_register_properties #(
            .DataWidth                ( DataWidth ),
            .data_t                   ( payload_t ),
            .CheckResetReleaseCover  ( width_idx == 0 )
        ) i_fall_through_register_properties (
            .clk_i   ( clk_i             ),
            .rst_ni  ( rst_ni            ),
            .clr_i   ( clr_i[Index]      ),
            .valid_i ( valid_i[Index]    ),
            .ready_o ( ready_o           ),
            .data_i  ( data_i[Index][DataWidth-1:0] ),
            .valid_o ( valid_o           ),
            .ready_i ( ready_i[Index]    ),
            .data_o  ( data_o            )
        );
    end

endmodule : cc_fall_through_register_formal
