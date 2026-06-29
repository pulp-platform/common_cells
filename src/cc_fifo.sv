// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

module cc_fifo #(
    parameter bit          FallThrough = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DataWidth   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned Depth       = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type         data_t      = logic [DataWidth-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    localparam int unsigned UsageWidth = cc_pkg::cnt_width(Depth)
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  clr_i,            // synchronous clear
    input  logic  flush_i,          // flush the queue
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  [UsageWidth-1:0] usage_o,  // fill pointer
    // as long as the queue is not full we can push new data
    input  data_t data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output data_t data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    // local parameter
    // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
    localparam int unsigned FifoDepth = (Depth > 0) ? Depth : 1;
    localparam int unsigned PtrWidth = cc_pkg::idx_width(Depth);
    // clock gating control
    logic gate_clock;
    // pointer to the read and write section of the queue
    logic [PtrWidth-1:0] read_pointer_n, read_pointer_q, write_pointer_n, write_pointer_q;
    // keep a counter to keep track of the current queue status
    // this integer will be truncated by the synthesis tool
    logic [UsageWidth-1:0] status_cnt_n, status_cnt_q;
    // actual memory
    data_t [FifoDepth - 1:0] mem_n, mem_q;

    assign usage_o = status_cnt_q;

    if (Depth == 0) begin : gen_pass_through
        assign empty_o     = ~push_i;
        assign full_o      = ~pop_i;
    end else begin : gen_fifo
        assign full_o       = (status_cnt_q == FifoDepth[UsageWidth-1:0]);
        assign empty_o      = (status_cnt_q == 0) & ~(FallThrough & push_i);
    end
    // status flags

    // read and write queue logic
    always_comb begin : read_write_comb
        // default assignment
        read_pointer_n  = read_pointer_q;
        write_pointer_n = write_pointer_q;
        status_cnt_n    = status_cnt_q;
        data_o          = (Depth == 0) ? data_i : mem_q[read_pointer_q];
        mem_n           = mem_q;
        gate_clock      = 1'b1;

        // push a new element to the queue
        if (push_i && ~full_o) begin
            // push the data onto the queue
            mem_n[write_pointer_q] = data_i;
            // un-gate the clock, we want to write something
            gate_clock = 1'b0;
            // increment the write counter
            // this is dead code when Depth is a power of two
            if (write_pointer_q == FifoDepth[PtrWidth-1:0] - 1)
                write_pointer_n = '0;
            else
                write_pointer_n = write_pointer_q + 1;
            // increment the overall counter
            status_cnt_n    = status_cnt_q + 1;
        end

        if (pop_i && ~empty_o) begin
            // read from the queue is a default assignment
            // but increment the read pointer...
            // this is dead code when Depth is a power of two
            if (read_pointer_n == FifoDepth[PtrWidth-1:0] - 1)
                read_pointer_n = '0;
            else
                read_pointer_n = read_pointer_q + 1;
            // ... and decrement the overall count
            status_cnt_n   = status_cnt_q - 1;
        end

        // keep the count pointer stable if we push and pop at the same time
        if (push_i && pop_i &&  ~full_o && ~empty_o)
            status_cnt_n   = status_cnt_q;

        // FIFO is in pass through mode -> do not change the pointers
        if (FallThrough && (status_cnt_q == 0) && push_i) begin
            data_o = data_i;
            if (pop_i) begin
                status_cnt_n = status_cnt_q;
                read_pointer_n = read_pointer_q;
                write_pointer_n = write_pointer_q;
            end
        end
    end

    // sequential process
    `FFARNC(read_pointer_q, read_pointer_n, clr_i || flush_i, '0, clk_i, rst_ni)
    `FFARNC(write_pointer_q, write_pointer_n, clr_i || flush_i, '0, clk_i, rst_ni)
    `FFARNC(status_cnt_q, status_cnt_n, clr_i || flush_i, '0, clk_i, rst_ni)

    `FFLARNC(mem_q, mem_n, !gate_clock, clr_i, {FifoDepth{data_t'('0)}}, clk_i, rst_ni)

`ifndef COMMON_CELLS_ASSERTS_OFF
    `ASSERT_INIT(depth_0, Depth > 0, "Depth must be greater than 0.")

    `ASSERT(full_write, full_o |-> ~push_i, clk_i, !rst_ni,
            "Trying to push new data although the FIFO is full.")

    `ASSERT(empty_read, empty_o |-> ~pop_i, clk_i, !rst_ni,
            "Trying to pop data although the FIFO is empty.")
`endif

endmodule // cc_fifo
