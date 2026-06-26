// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_ring_buffer instead.

module ring_buffer #(
  parameter int unsigned Depth  = 32,
  parameter type         data_t = logic
) (
  input  logic                                        clk_i,
  input  logic                                        rst_ni,
  input  logic                                        wvalid_i,
  output logic                                        wready_o,
  input  data_t                                       wdata_i,
  input  logic                                        rvalid_i,
  output logic                                        rready_o,
  input  logic [cc_pkg::idx_width(Depth)-1:0]   raddr_i,
  output data_t                                       rdata_o,
  input  logic                                        advance_i,
  input  logic [cc_pkg::idx_width(Depth+1)-1:0] step_i,
  output logic [cc_pkg::idx_width(Depth)-1:0]   wptr_o,
  output logic [cc_pkg::idx_width(Depth)-1:0]   rptr_o,
  output logic                                        full_o,
  output logic                                        empty_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_ring_buffer' instead.");
  // synthesis translate_on
  cc_ring_buffer #(
    .Depth  ( Depth  ),
    .data_t ( data_t )
  ) i_cc_ring_buffer (
    .clk_i    ( clk_i    ),
    .rst_ni   ( rst_ni   ),
    .wvalid_i ( wvalid_i ),
    .wready_o ( wready_o ),
    .wdata_i  ( wdata_i  ),
    .rvalid_i ( rvalid_i ),
    .rready_o ( rready_o ),
    .raddr_i  ( raddr_i  ),
    .rdata_o  ( rdata_o  ),
    .advance_i( advance_i),
    .step_i   ( step_i   ),
    .wptr_o   ( wptr_o   ),
    .rptr_o   ( rptr_o   ),
    .full_o   ( full_o   ),
    .empty_o  ( empty_o  )
  );
endmodule
