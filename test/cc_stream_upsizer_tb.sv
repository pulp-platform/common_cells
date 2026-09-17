// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Lorenzo Leone <lleone@iis.ee.ethz.ch>

/// Testbench for cc_stream_upsizer
module cc_stream_upsizer_tb #(
  parameter int unsigned NarrowWidth = 8,
  parameter int unsigned WideWidth   = 32,
  localparam int unsigned Ratio      = WideWidth / NarrowWidth
);

  logic clk, rst_n;
  logic inp_valid, inp_ready;
  logic oup_valid, oup_ready;

  logic [NarrowWidth-1:0] inp_data;
  logic [  WideWidth-1:0] oup_data;

  int unsigned nr_checks;

  cc_stream_upsizer #(
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
  initial begin
    automatic logic [NarrowWidth-1:0] beat;

    cb.inp_valid <= 1'b0;
    wait (rst_n == 1'b1);

    forever begin
      beat = $urandom();
      repeat ($urandom_range(0, 4)) @(cb);
      cb.inp_data  <= beat;
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
  // Every `Ratio` accepted narrow beats assemble one expected wide word,
  // LSB-first, matching the DUT's own slicing order.
  logic [WideWidth-1:0] queue[$];

  initial begin
    automatic logic [WideWidth-1:0]   partial;
    automatic int unsigned            slice_cnt;
    automatic logic [WideWidth-1:0]   expected;

    nr_checks = 0;
    slice_cnt = 0;
    partial   = '0;

    forever begin
      @(pck);

      if (pck.inp_valid && pck.inp_ready) begin
        partial[slice_cnt*NarrowWidth+:NarrowWidth] = pck.inp_data;
        slice_cnt++;
        if (slice_cnt == Ratio) begin
          queue.push_back(partial);
          slice_cnt = 0;
          partial   = '0;
        end
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
