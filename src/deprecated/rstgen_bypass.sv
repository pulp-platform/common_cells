// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_rstgen_bypass instead.

module rstgen_bypass #(
  parameter int unsigned NumRegs = 4
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic rst_test_mode_ni,
  input  logic test_mode_i,
  output logic rst_no,
  output logic init_no
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_rstgen_bypass' instead.");
  // synthesis translate_on
  cc_rstgen_bypass #(
    .NumRegs ( NumRegs )
  ) i_cc_rstgen_bypass (
    .clk_i            ( clk_i            ),
    .rst_ni           ( rst_ni           ),
    .rst_test_mode_ni ( rst_test_mode_ni ),
    .test_mode_i      ( test_mode_i      ),
    .rst_no           ( rst_no           ),
    .init_no          ( init_no          )
  );
endmodule
