// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_demux instead.

module stream_demux #(
  parameter int unsigned N_OUP     = 32'd1,
  // Derived parameter (kept for backward compatibility, do not override)
  parameter int unsigned LOG_N_OUP = (N_OUP > 32'd1) ? unsigned'($clog2(N_OUP)) : 1'b1
) (
  input  logic               inp_valid_i,
  output logic               inp_ready_o,
  input  logic [LOG_N_OUP-1:0] oup_sel_i,
  output logic [N_OUP-1:0]   oup_valid_o,
  input  logic [N_OUP-1:0]   oup_ready_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_stream_demux' instead.");
  // synthesis translate_on
  // Note: LOG_N_OUP is a localparam in cc_stream_demux, not passed.
  cc_stream_demux #(
    .NumOup ( N_OUP )
  ) i_cc_stream_demux (
    .inp_valid_i ( inp_valid_i ),
    .inp_ready_o ( inp_ready_o ),
    .oup_sel_i   ( oup_sel_i   ),
    .oup_valid_o ( oup_valid_o ),
    .oup_ready_i ( oup_ready_i )
  );
endmodule
