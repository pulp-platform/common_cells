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

    assign wready_o = !full_o;
    assign rdata_o = mem_q[raddr_i];

    ////////////////
    // Assertions //
    ////////////////

    // TODO check that read pointer never surpasses write pointer
    // TODO check that write pointer never "doubles" read pointer

endmodule
