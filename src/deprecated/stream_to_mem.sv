// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_to_mem instead.

module stream_to_mem #(
  parameter type         mem_req_t  = logic,
  parameter type         mem_resp_t = logic,
  parameter int unsigned BufDepth   = 32'd1
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  input  mem_req_t  req_i,
  input  logic      req_valid_i,
  output logic      req_ready_o,
  output mem_resp_t resp_o,
  output logic      resp_valid_o,
  input  logic      resp_ready_i,
  output mem_req_t  mem_req_o,
  output logic      mem_req_valid_o,
  input  logic      mem_req_ready_i,
  input  mem_resp_t mem_resp_i,
  input  logic      mem_resp_valid_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_to_mem' instead.");
  // synthesis translate_on
  cc_stream_to_mem #(
    .mem_req_t  ( mem_req_t  ),
    .mem_resp_t ( mem_resp_t ),
    .BufDepth   ( BufDepth   )
  ) i_cc_stream_to_mem (
    .clk_i            ( clk_i            ),
    .rst_ni           ( rst_ni           ),
    .req_i            ( req_i            ),
    .req_valid_i      ( req_valid_i      ),
    .req_ready_o      ( req_ready_o      ),
    .resp_o           ( resp_o           ),
    .resp_valid_o     ( resp_valid_o     ),
    .resp_ready_i     ( resp_ready_i     ),
    .mem_req_o        ( mem_req_o        ),
    .mem_req_valid_o  ( mem_req_valid_o  ),
    .mem_req_ready_i  ( mem_req_ready_i  ),
    .mem_resp_i       ( mem_resp_i       ),
    .mem_resp_valid_i ( mem_resp_valid_i )
  );
endmodule
