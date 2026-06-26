// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_ecc_encode instead.
// Note: type parameters (data_t, parity_t, code_word_t, encoded_data_t) are now
// localparams in cc_ecc_encode, derived from DataWidth using cc_pkg functions.
module ecc_encode #(
  parameter int unsigned DataWidth     = 64,
  parameter type data_t                = logic [DataWidth-1:0],
  parameter type parity_t              = logic [cc_pkg::ecc_get_parity_width(DataWidth)-1:0],
  parameter type code_word_t           = logic [cc_pkg::ecc_get_cw_width(DataWidth)-1:0],
  parameter type encoded_data_t        = struct packed {
    logic [cc_pkg::ecc_get_parity_width(DataWidth)-1:0] parity;
    logic [DataWidth-1:0]                                data;
  }
)(
  input  data_t         data_i,
  output encoded_data_t data_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_ecc_encode' instead.");
  // synthesis translate_on
  cc_ecc_encode #(
    .DataWidth ( DataWidth )
  ) i_cc_ecc_encode (
    .data_i ( data_i ),
    .data_o ( data_o )
  );
endmodule
