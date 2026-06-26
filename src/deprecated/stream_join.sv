// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_join instead.

module stream_join #(
  parameter int unsigned N_INP = 32'd0
) (
  input  logic [N_INP-1:0] inp_valid_i,
  output logic [N_INP-1:0] inp_ready_o,
  output logic             oup_valid_o,
  input  logic             oup_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_join' instead.");
  // synthesis translate_on
  cc_stream_join #(
    .N_INP ( N_INP )
  ) i_cc_stream_join (
    .inp_valid_i ( inp_valid_i ),
    .inp_ready_o ( inp_ready_o ),
    .oup_valid_o ( oup_valid_o ),
    .oup_ready_i ( oup_ready_i )
  );
endmodule
