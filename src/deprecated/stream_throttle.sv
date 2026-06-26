// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_throttle instead.

module stream_throttle #(
  parameter int unsigned MaxNumPending = 1,
  // Derived parameters (kept for backward compatibility, do not override)
  parameter int unsigned CntWidth      = cc_pkg::idx_width(MaxNumPending),
  parameter type         credit_t      = logic [CntWidth-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  input  logic    req_valid_i,
  output logic    req_valid_o,
  input  logic    req_ready_i,
  output logic    req_ready_o,
  input  logic    rsp_valid_i,
  input  logic    rsp_ready_i,
  input  credit_t credit_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_throttle' instead.");
  // synthesis translate_on
  // Note: CntWidth and credit_t are localparams in cc_stream_throttle, not passed.
  cc_stream_throttle #(
    .MaxNumPending ( MaxNumPending )
  ) i_cc_stream_throttle (
    .clk_i       ( clk_i       ),
    .rst_ni      ( rst_ni      ),
    .req_valid_i ( req_valid_i ),
    .req_valid_o ( req_valid_o ),
    .req_ready_i ( req_ready_i ),
    .req_ready_o ( req_ready_o ),
    .rsp_valid_i ( rsp_valid_i ),
    .rsp_ready_i ( rsp_ready_i ),
    .credit_i    ( credit_i    )
  );
endmodule
