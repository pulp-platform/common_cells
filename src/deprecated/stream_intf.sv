// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_stream_dv instead.
`include "common_cells/assertions.svh"

interface STREAM_DV #(
  parameter type payload_t = logic
)(
  input logic clk_i
);
  payload_t data;
  logic valid;
  logic ready;

  modport In (
    output ready,
    input valid, data
  );

  modport Out (
    output valid, data,
    input ready
  );

  modport Passive (
    input valid, ready, data
  );

  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT(data_unstable, (valid && !ready |=> $stable(data)), clk_i, 1'b0)
  `ASSERT(valid_unstable, (valid && !ready |=> valid), clk_i, 1'b0)
  `endif
endinterface
