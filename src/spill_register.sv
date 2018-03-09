// Copyright (c) 2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>


/// A register with handshakes that completely cuts any combinational paths
/// between the input and output.
module spill_register #(
  parameter type T = logic
)(
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic valid_i ,
  output logic ready_o ,
  input  T     data_i  ,
  output logic valid_o ,
  input  logic ready_i ,
  output T     data_o
);

  // The A register.
  T a_data_q;
  logic a_full_q;
  logic a_fill, a_drain;
  logic a_en, a_en_data;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_data
    if (!rst_ni)
      a_data_q <= '0;
    else if (a_fill)
      a_data_q <= data_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_full
    if (!rst_ni)
      a_full_q <= 0;
    else if (a_fill || a_drain)
      a_full_q <= a_fill;
  end

  // The B register.
  T b_data_q;
  logic b_full_q;
  logic b_fill, b_drain;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_data
    if (!rst_ni)
      b_data_q <= '0;
    else if (b_fill)
      b_data_q <= a_data_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_full
    if (!rst_ni)
      b_full_q <= 0;
    else if (b_fill || b_drain)
      b_full_q <= b_fill;
  end

  // Fill the A register when the A or B register is empty. Drain the A register
  // whenever it is full and being filled.
  assign a_fill = valid_i && ready_o;
  assign a_drain = a_full_q && !b_full_q;

  // Fill the B register whenever the A register is drained, but the downstream
  // circuit is not ready. Drain the B register whenever it is full and the
  // downstream circuit is ready.
  assign b_fill = a_drain && !ready_i;
  assign b_drain = b_full_q && ready_i;

  // We can accept input as long as register B is not full.
  assign ready_o = !a_full_q || !b_full_q;

  // The unit provides output as long as one of the registers is filled.
  assign valid_o = a_full_q | b_full_q;

  // We empty the spill register before the slice register.
  assign data_o = b_full_q ? b_data_q : a_data_q;

endmodule
