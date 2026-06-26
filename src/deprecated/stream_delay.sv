// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_delay instead.

module stream_delay #(
  parameter bit          StallRandom = 0,
  parameter int          FixedDelay  = 1,
  parameter type         payload_t   = logic,
  parameter logic [15:0] Seed        = '0
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  payload_t payload_i,
  output logic     ready_o,
  input  logic     valid_i,
  output payload_t payload_o,
  input  logic     ready_i,
  output logic     valid_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_delay' instead.");
  // synthesis translate_on
  cc_stream_delay #(
    .StallRandom ( StallRandom ),
    .FixedDelay  ( FixedDelay  ),
    .payload_t   ( payload_t   ),
    .Seed        ( Seed        )
  ) i_cc_stream_delay (
    .clk_i     ( clk_i     ),
    .rst_ni    ( rst_ni    ),
    .payload_i ( payload_i ),
    .ready_o   ( ready_o   ),
    .valid_i   ( valid_i   ),
    .payload_o ( payload_o ),
    .ready_i   ( ready_i   ),
    .valid_o   ( valid_o   )
  );
endmodule
