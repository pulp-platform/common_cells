// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software and hardware distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Elaboration harness for representative FIFO parametrizations.  Every
// instance is checked through its public interface by cc_fifo_properties.
module cc_fifo_formal import cc_pkg::*; (
    input logic             clk_i,
    input logic             rst_ni,
    input logic [7:0]       clr_i,
    input logic [7:0]       flush_i,
    input logic [7:0]       push_i,
    input logic [7:0]       pop_i,
    input logic [7:0][1:0]  data_i
);

    typedef logic [1:0] payload_t;

    for (genvar depth = 1; depth <= 4; depth++) begin : gen_depth
        for (genvar fall_through = 0; fall_through <= 1; fall_through++) begin : gen_mode
            localparam int unsigned Depth = unsigned'(depth);
            localparam bit FallThrough = bit'(fall_through);
            localparam int unsigned Index = (depth - 1) * 2 + fall_through;
            localparam int unsigned UsageWidth = cc_pkg::cnt_width(Depth);

            logic full;
            logic empty;
            logic [UsageWidth-1:0] usage;
            payload_t data_o;

            cc_fifo #(
                .FallThrough ( FallThrough ),
                .DataWidth   ( 2           ),
                .Depth       ( Depth       ),
                .data_t      ( payload_t   )
            ) i_fifo (
                .clk_i    ( clk_i          ),
                .rst_ni   ( rst_ni         ),
                .clr_i    ( clr_i[Index]   ),
                .flush_i  ( flush_i[Index] ),
                .full_o   ( full           ),
                .empty_o  ( empty          ),
                .usage_o  ( usage          ),
                .data_i   ( data_i[Index]  ),
                .push_i   ( push_i[Index]  ),
                .data_o   ( data_o         ),
                .pop_i    ( pop_i[Index]   )
            );

            cc_fifo_properties #(
                .FallThrough ( FallThrough ),
                .DataWidth   ( 2           ),
                .Depth       ( Depth       ),
                .data_t      ( payload_t   ),
                .CheckResetReleaseCover ( Index == 0 )
            ) i_fifo_properties (
                .clk_i   ( clk_i          ),
                .rst_ni  ( rst_ni         ),
                .clr_i   ( clr_i[Index]   ),
                .flush_i ( flush_i[Index] ),
                .full_o  ( full           ),
                .empty_o ( empty          ),
                .usage_o ( usage          ),
                .data_i  ( data_i[Index]  ),
                .push_i  ( push_i[Index]  ),
                .data_o  ( data_o         ),
                .pop_i   ( pop_i[Index]   )
            );
        end
    end

endmodule : cc_fifo_formal
