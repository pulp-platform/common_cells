// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

/// Testbench for cc_stream_downsizer
module cc_stream_downsizer_tb #(
  parameter int unsigned NarrowWidth = 8,
  parameter int unsigned WideWidth   = 32,
  parameter int unsigned NumChecks   = 32'd100000,
  localparam int unsigned Ratio      = WideWidth / NarrowWidth
);

  localparam time TClk = 10ns;
  localparam time TA   = TClk / 4;
  localparam time TT   = TClk * 3 / 4;

  logic clk, rst_n;
  logic inp_valid, inp_ready;
  logic oup_valid, oup_ready;

  logic [  WideWidth-1:0] inp_data;
  logic [NarrowWidth-1:0] oup_data;

  clk_rst_gen #(
    .ClkPeriod   (TClk),
    .RstClkCycles(5)
  ) i_clk_rst_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  // Randomized narrow-side manager.
  rand_stream_mst #(
    .data_t       (logic [WideWidth-1:0]),
    .MinWaitCycles(0),
    .MaxWaitCycles(8),
    .ApplDelay    (TA),
    .AcqDelay     (TT)
  ) i_rand_stream_mst (
    .clk_i  (clk),
    .rst_ni (rst_n),
    .data_o (inp_data),
    .valid_o(inp_valid),
    .ready_i(inp_ready)
  );

  // Randomized narrow-side consumer.
  rand_stream_slv #(
    .data_t       (logic [NarrowWidth-1:0]),
    .MinWaitCycles(1),
    .MaxWaitCycles(8),
    .ApplDelay    (TA),
    .AcqDelay     (TT)
  ) i_rand_stream_slv (
    .clk_i  (clk),
    .rst_ni (rst_n),
    .data_i (oup_data),
    .valid_i(oup_valid),
    .ready_o(oup_ready)
  );

  cc_stream_downsizer #(
    .NarrowWidth(NarrowWidth),
    .WideWidth  (WideWidth)
  ) dut (
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .inp_data_i (inp_data),
    .inp_valid_i(inp_valid),
    .inp_ready_o(inp_ready),
    .oup_data_o (oup_data),
    .oup_valid_o(oup_valid),
    .oup_ready_i(oup_ready)
  );

  // -------------------
  // Monitor && Checker
  // -------------------
  // A new wide word expands into `Ratio` expected narrow slices, LSB-first,
  // matching the DUT's own slicing order. Since the DUT never registers the
  // wide word (it re-reads `inp_data_i` for every slice off the still-valid
  // input), the first slice is already observable at the output the cycle
  // the word is first presented - well before it's fully *accepted* on the
  // last slice. So the expected slices must be pushed at word-start (first
  // cycle `inp_valid` is high for a new word), not at word-accept.
  logic [NarrowWidth-1:0] queue[$];

  initial begin
    automatic logic [NarrowWidth-1:0] expected;
    automatic logic                   word_pending;
    automatic int unsigned            nr_checks;
    nr_checks    = 0;
    word_pending = 1'b0;

    wait (rst_n);
    forever begin
      @(posedge clk);
      #TT;

      if (inp_valid && !word_pending) begin
        for (int unsigned k = 0; k < Ratio; k++) begin
          queue.push_back(inp_data[k*NarrowWidth+:NarrowWidth]);
        end
        word_pending = 1'b1;
      end

      if (inp_valid && inp_ready) begin
        word_pending = 1'b0;
      end

      if (oup_valid && oup_ready) begin
        expected = queue.pop_front();
        assert (expected == oup_data)
        else $error("Mismatch, Expected: %0h Got %0h", expected, oup_data);
        nr_checks++;
      end

      if (nr_checks >= NumChecks) begin
        $display("Checked %0d stimuli", nr_checks);
        $finish(0);
      end
    end
  end

endmodule
