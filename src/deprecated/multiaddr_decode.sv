// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_multiaddr_decode instead.

module multiaddr_decode #(
  parameter int unsigned NoIndices = 32'd1,
  parameter int unsigned NoRules   = 32'd1,
  parameter type         addr_t    = logic,
  parameter int unsigned IdxWidth  = cc_pkg::idx_width(NoIndices),
  parameter type         idx_t     = logic [IdxWidth-1:0],
  // verilog_lint: waive typedef-structs-unions
  parameter type         rule_t    = struct packed {
    idx_t  idx;
    addr_t addr;
    addr_t mask;
  }
) (
  input  addr_t                 addr_i,
  input  addr_t                 mask_i,
  input  rule_t [NoRules-1:0]   addr_map_i,
  output logic  [NoIndices-1:0] select_o,
  output addr_t [NoIndices-1:0] addr_o,
  output addr_t [NoIndices-1:0] mask_o,
  output logic                  dec_valid_o,
  output logic                  dec_error_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_multiaddr_decode' instead.");
  // synthesis translate_on
  cc_multiaddr_decode #(
    .NoIndices ( NoIndices ),
    .NoRules   ( NoRules   ),
    .addr_t    ( addr_t    ),
    .IdxWidth  ( IdxWidth  ),
    .idx_t     ( idx_t     ),
    .rule_t    ( rule_t    )
  ) i_cc_multiaddr_decode (
    .addr_i           ( addr_i      ),
    .mask_i           ( mask_i      ),
    .addr_map_i       ( addr_map_i  ),
    .select_o         ( select_o    ),
    .addr_o           ( addr_o      ),
    .mask_o           ( mask_o      ),
    .dec_valid_o      ( dec_valid_o ),
    .dec_error_o      ( dec_error_o ),
    .en_default_idx_i ( 1'b0        ),
    .default_idx_i    ( '0          )
  );
endmodule
