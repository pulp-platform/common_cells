// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_addr_decode instead.

module addr_decode #(
  parameter int unsigned NoIndices = 32'd0,
  parameter int unsigned NoRules   = 32'd1,
  parameter type         addr_t    = logic,
  parameter bit          Napot     = 0,
  parameter int unsigned IdxWidth  = cc_pkg::idx_width(NoIndices),
  parameter type         idx_t     = logic [IdxWidth-1:0],
  // verilog_lint: waive typedef-structs-unions
  parameter type         rule_t    = struct packed {
    idx_t  idx;
    addr_t start_addr;
    addr_t end_addr;
  }
) (
  input  addr_t               addr_i,
  input  rule_t [NoRules-1:0] addr_map_i,
  output idx_t                idx_o,
  output logic                dec_valid_o,
  output logic                dec_error_o,
  input  logic                en_default_idx_i,
  input  idx_t                default_idx_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_addr_decode' instead.");
  // synthesis translate_on
  cc_addr_decode #(
    .NoIndices ( NoIndices ),
    .NoRules   ( NoRules   ),
    .addr_t    ( addr_t    ),
    .rule_t    ( rule_t    ),
    .Napot     ( Napot     ),
    .IdxWidth  ( IdxWidth  ),
    .idx_t     ( idx_t     )
  ) i_cc_addr_decode (
    .addr_i           ( addr_i           ),
    .addr_map_i       ( addr_map_i       ),
    .idx_o            ( idx_o            ),
    .dec_valid_o      ( dec_valid_o      ),
    .dec_error_o      ( dec_error_o      ),
    .en_default_idx_i ( en_default_idx_i ),
    .default_idx_i    ( default_idx_i    )
  );
endmodule
