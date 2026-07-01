// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_lfsr instead.

module lfsr #(
  parameter int unsigned LfsrWidth    = 64,
  parameter int unsigned OutWidth     = 8,
  parameter logic [LfsrWidth-1:0] RstVal = '1,
  parameter int unsigned CipherLayers = 0,
  parameter bit          CipherReg   = 1'b1
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic               en_i,
  output logic [OutWidth-1:0] out_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_lfsr' instead.");
  // synthesis translate_on
  cc_lfsr #(
    .LfsrWidth    ( LfsrWidth    ),
    .OutWidth     ( OutWidth     ),
    .RstVal       ( RstVal       ),
    .CipherLayers ( CipherLayers ),
    .CipherReg    ( CipherReg    )
  ) i_cc_lfsr (
    .clk_i  ( clk_i  ),
    .rst_ni ( rst_ni ),
    .clr_i  ( 1'b0  ),
    .en_i   ( en_i   ),
    .out_o  ( out_o  )
  );
endmodule
