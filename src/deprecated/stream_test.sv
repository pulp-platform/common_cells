// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_test_pkg::cc_stream_driver instead.
// Stream test package using the deprecated STREAM_DV interface name.
package stream_test;

  // synthesis translate_off
  class stream_driver #(
    parameter type payload_t = logic,
    parameter time TA = 2ns,
    parameter time TT = 8ns
  );
    virtual STREAM_DV #(
      .payload_t (payload_t)
    ) stream;

    function new (
      virtual STREAM_DV #(
        .payload_t (payload_t)
      ) stream
    );
      this.stream = stream;
    endfunction

    function void reset_in();
      stream.valid = 1'b0;
    endfunction

    function void reset_out();
      stream.ready = 1'b0;
    endfunction

    task automatic cycle_start;
      #TT;
    endtask

    task automatic cycle_end;
      @(posedge stream.clk_i);
    endtask

    task automatic send (input payload_t data);
      stream.data  <= #TA data;
      stream.valid <= #TA 1'b1;
      cycle_start();
      while (stream.ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      stream.valid <= #TA 1'b0;
    endtask

    task automatic recv(output payload_t data);
      stream.ready <= #TA 1'b1;
      cycle_start();
      while (stream.valid != 1) begin cycle_end(); cycle_start(); end
      data = stream.data;
      cycle_end();
      stream.ready <= #TA 1'b0;
    endtask
  endclass
  // synthesis translate_on

endpackage : stream_test
