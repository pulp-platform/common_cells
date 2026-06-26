// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_addr_decode_napot instead.

module addr_decode_napot #(
  parameter int unsigned NoIndices = 32'd0,
  parameter int unsigned NoRules   = 32'd0,
  parameter type         addr_t    = logic,
  parameter type         rule_t    = logic,
  parameter int unsigned IdxWidth  = cc_pkg::idx_width(NoIndices),
  parameter type         idx_t     = logic [IdxWidth-1:0]
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
  initial $warning("Module '%m' is deprecated. Use 'cc_addr_decode_napot' instead.");
  // synthesis translate_on
  // Note: IdxWidth and idx_t are localparams in cc_addr_decode_napot, not passed.
  cc_addr_decode_napot #(
    .NoIndices ( NoIndices ),
    .NoRules   ( NoRules   ),
    .addr_t    ( addr_t    ),
    .rule_t    ( rule_t    )
  ) i_cc_addr_decode_napot (
    .addr_i           ( addr_i           ),
    .addr_map_i       ( addr_map_i       ),
    .idx_o            ( idx_o            ),
    .dec_valid_o      ( dec_valid_o      ),
    .dec_error_o      ( dec_error_o      ),
    .en_default_idx_i ( en_default_idx_i ),
    .default_idx_i    ( default_idx_i    )
  );
endmodule
