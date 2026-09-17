// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

/// Testbench for cc_stream_downsizer
module cc_stream_downsizer_tb #(
  parameter int unsigned NarrowWidth = 8,
  parameter int unsigned WideWidth   = 32,
  localparam int unsigned Ratio      = WideWidth / NarrowWidth
);

  logic clk, rst_n;
  logic inp_valid, inp_ready;
  logic oup_valid, oup_ready;

  logic [  WideWidth-1:0] inp_data;
  logic [NarrowWidth-1:0] oup_data;

  int unsigned nr_checks;

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

  initial begin
    clk = 1'b0;
    rst_n = 1'b0;
    repeat (8) #10ns clk = ~clk;

    rst_n = 1'b1;
    forever #10ns clk = ~clk;
  end

  // simulator stopper, this is suboptimal better go for coverage
  initial begin
    #100ms
    $display("Checked %0d stimuli", nr_checks);
    $stop;
  end

  // clocking outputs are DUT inputs and vice versa
  clocking cb @(posedge clk);
    default input #2 output #4;
    output inp_data, inp_valid, oup_ready;
    input inp_ready, oup_valid, oup_data;
  endclocking

  clocking pck @(posedge clk);
    default input #2 output #4;
    input inp_data, inp_valid, inp_ready, oup_data, oup_valid, oup_ready;
  endclocking

  // --------
  // Driver
  // --------
  // Holds `inp_data`/`inp_valid` stable while waiting for `inp_ready`, per the
  // handshake contract the downsizer itself relies on (it re-reads `inp_data_i`
  // for every slice instead of registering it).
  initial begin
    automatic logic [WideWidth-1:0] word;

    cb.inp_valid <= 1'b0;
    wait (rst_n == 1'b1);

    forever begin
      word = {$urandom(), $urandom()};
      repeat ($urandom_range(0, 4)) @(cb);
      cb.inp_data  <= word;
      cb.inp_valid <= 1'b1;
      @(cb);
      while (!cb.inp_ready) @(cb);
      cb.inp_valid <= 1'b0;
    end
  end

  // --------
  // Consumer
  // --------
  initial begin
    wait (rst_n == 1'b1);
    forever begin
      @(cb);
      cb.oup_ready <= 1'b1;
      repeat ($urandom_range(0, 4)) @(cb);
      cb.oup_ready <= 1'b0;
    end
  end

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
    automatic logic word_pending;
    nr_checks = 0;
    word_pending = 1'b0;

    forever begin
      @(pck);

      if (pck.inp_valid && !word_pending) begin
        for (int unsigned k = 0; k < Ratio; k++) begin
          queue.push_back(pck.inp_data[k*NarrowWidth+:NarrowWidth]);
        end
        word_pending = 1'b1;
      end

      if (pck.inp_valid && pck.inp_ready) begin
        word_pending = 1'b0;
      end

      if (pck.oup_valid && pck.oup_ready) begin
        expected = queue.pop_front();
        assert (expected == pck.oup_data)
        else $error("Mismatch, Expected: %0h Got %0h", expected, pck.oup_data);
        nr_checks++;
      end
    end
  end

endmodule
