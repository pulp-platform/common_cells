// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module ring_buffer #(
    parameter int unsigned Depth = 32,
    parameter type data_t = logic,
    /// Derived parameter *Do not override*
    localparam int unsigned AddrWidth = cf_math_pkg::idx_width(Depth),
    localparam int unsigned StepWidth = cf_math_pkg::idx_width(Depth+1),
    localparam type addr_t = logic [AddrWidth-1:0],
    localparam type step_t = logic [StepWidth-1:0]
) (
    input logic clk_i,
    input logic rst_ni,

    // Write interface
    input logic wvalid_i,
    output logic wready_o,
    input data_t wdata_i,

    // Restricted random access read interface
    input logic rvalid_i,
    output logic rready_o,
    input addr_t raddr_i,
    output data_t rdata_o,

    // Flexible read pointer increment interface
    input logic advance_i,
    input step_t step_i,

    // Status signals
    output addr_t wptr_o,
    output addr_t rptr_o,
    output logic full_o,
    output logic empty_o
);

    ///////////
    // State //
    ///////////

    data_t [Depth-1:0] mem_d, mem_q;

    // We allocate one more bit than needed to represent memory
    // addresses, to compute full/empty status of the buffer.
    logic [AddrWidth:0] rptr_d, rptr_q;
    logic [AddrWidth:0] wptr_d, wptr_q;

    `FF(mem_q, mem_d, '0, clk_i, rst_ni)
    `FF(rptr_q, rptr_d, '0, clk_i, rst_ni)
    `FF(wptr_q, wptr_d, '0, clk_i, rst_ni)

    ////////////////////////////
    // State transition logic //
    ////////////////////////////

    always_comb begin
        // Default assignments
        mem_d = mem_q;
        rptr_d = rptr_q;
        wptr_d = wptr_q;

        // Write logic
        if (wvalid_i && wready_o) begin
            mem_d[wptr_q[AddrWidth-1:0]] = wdata_i;
            wptr_d = wptr_q + 1;
        end

        // Read pointer increment logic
        if (advance_i) begin
            rptr_d = rptr_q + step_i;
        end
    end

    //////////////////
    // Output logic //
    //////////////////

    assign wptr_o = wptr_q[AddrWidth-1:0];
    assign rptr_o = rptr_q[AddrWidth-1:0];

    assign empty_o = wptr_q == rptr_q;
    assign full_o = (wptr_q[AddrWidth-1:0] == rptr_q[AddrWidth-1:0]) && !empty_o;

    // A read request can only be accepted if it is within the range of
    // valid instructions (i.e. between the read and write pointers).
    // This ready signal is provided as a backpressure mechanism to wait
    // for the write pointer to advance, until the requested instruction
    // is present in the ring buffer.
    // When rptr_o < wptr_o, the valid range is [rptr_o, wptr_o).
    // When rptr_o > wptr_o (wrap-around), the valid range is [rptr_o, Depth) U [0, wptr_o).
    // When rptr_o == wptr_o and !empty (buffer is full), all addresses are valid.
    assign rready_o = ((rptr_o < wptr_o) && ((raddr_i >= rptr_o) && (raddr_i < wptr_o))) ||
                      ((rptr_o > wptr_o) && ((raddr_i >= rptr_o) || (raddr_i < wptr_o))) ||
                      ((rptr_o == wptr_o) && !empty_o);

    assign wready_o = !full_o;
    assign rdata_o = mem_q[raddr_i];

    ////////////////
    // Assertions //
    ////////////////

    // When rptr_o < wptr_o, the valid range is [rptr_o, wptr_o).
    // When rptr_o > wptr_o (wrap-around), the valid range is [rptr_o, Depth) U [0, wptr_o).
    // When rptr_o == wptr_o and !empty (buffer is full), all addresses are valid.
    `ASSERT(
        ReadAddrOutOfBounds,
        rvalid_i && rready_o |->
        (
            ((rptr_o < wptr_o) && ((raddr_i >= rptr_o) && (raddr_i < wptr_o))) ||
            ((rptr_o > wptr_o) && ((raddr_i >= rptr_o) || (raddr_i < wptr_o))) ||
            ((rptr_o == wptr_o) && !empty_o)
        ),
        clk_i, !rst_ni,
        "raddr_i is not within the valid range defined by rptr_o and wptr_o"
    );

    // TODO check that read pointer never surpasses write pointer
    // TODO check that write pointer never "doubles" read pointer
    // TODO add interfaces stable assertions

endmodule
