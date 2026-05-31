// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Georg Rutishauser <georgr@iis.ee.ethz.ch>

module cc_stream_fifo #(
    /// FIFO is in fall-through mode
    parameter bit          FallThrough = 1'b0,
    /// Default data width if the fifo is of type logic
    parameter int unsigned DataWidth   = 32,
    /// Depth can be arbitrary from 0 to 2**32
    parameter int unsigned Depth       = 8,
    parameter type         data_t      = logic [DataWidth-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    localparam int unsigned AddrDepth  = (Depth > 1) ? $clog2(Depth) : 1
) (
    input  logic                 clk_i,      // Clock
    input  logic                 rst_ni,     // Asynchronous reset active low
    input  logic                 flush_i,    // flush the fifo
    output logic [AddrDepth-1:0] usage_o,    // fill pointer
    // input interface
    input  data_t                data_i,     // data to push into the fifo
    input  logic                 valid_i,    // input data valid
    output logic                 ready_o,    // fifo is not full
    // output interface
    output data_t                data_o,     // output data
    output logic                 valid_o,    // fifo is not empty
    input  logic                 ready_i     // pop head from fifo
);

    logic push, pop;
    logic empty, full;

    assign push    = valid_i & ~full;
    assign pop     = ready_i & ~empty;
    assign ready_o = ~full;
    assign valid_o = ~empty;

    cc_fifo #(
        .FallThrough(FallThrough),
        .DataWidth  (DataWidth),
        .Depth      (Depth),
        .data_t     (data_t)
    ) fifo_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .full_o (full),
        .empty_o(empty),
        .usage_o,
        .data_i,
        .push_i (push),
        .data_o,
        .pop_i  (pop)
    );

endmodule
