// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_credit_counter instead.

module credit_counter #(
  parameter int unsigned NumCredits      = 0,
  parameter bit          InitCreditEmpty = 1'b0,
  // Derived parameters (kept for backward compatibility, do not override)
  parameter int unsigned InitNumCredits  = InitCreditEmpty ? '0 : NumCredits,
  parameter type         credit_cnt_t    = logic [$clog2(NumCredits):0]
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  output credit_cnt_t  credit_o,
  input  logic         credit_give_i,
  input  logic         credit_take_i,
  input  logic         credit_init_i,
  output logic         credit_left_o,
  output logic         credit_crit_o,
  output logic         credit_full_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_credit_counter' instead.");
  // synthesis translate_on
  // Note: InitNumCredits and credit_cnt_t are localparams in cc_credit_counter, not passed.
  cc_credit_counter #(
    .NumCredits      ( NumCredits      ),
    .InitCreditEmpty ( InitCreditEmpty )
  ) i_cc_credit_counter (
    .clk_i         ( clk_i         ),
    .rst_ni        ( rst_ni        ),
    .credit_o      ( credit_o      ),
    .credit_give_i ( credit_give_i ),
    .credit_take_i ( credit_take_i ),
    .clr_i         ( credit_init_i ),
    .credit_left_o ( credit_left_o ),
    .credit_crit_o ( credit_crit_o ),
    .credit_full_o ( credit_full_o )
  );
endmodule
