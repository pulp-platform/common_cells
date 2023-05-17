//-----------------------------------------------------------------------------
// Copyright (C) 2023 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//-----------------------------------------------------------------------------

// Author: Manuel Eggimann <meggimann@iis.ee.ethz.ch>

module stream_deposit_tb #(
    /// Theu number of requests to simulate
    parameter int unsigned NumReq   = 32'd10000,
    /// Clock cycle time.
    parameter time         CyclTime = 20ns
);

  logic clk;
  logic rst_n;

  localparam type payload_t = logic [$clog2(NumReq)-1:0];



  // clock generator
  clk_rst_gen #(
      .ClkPeriod   (CyclTime),
      .RstClkCycles(5)
  ) i_clk_rst_gen (
      .clk_o (clk),
      .rst_no(rst_n)
  );

  typedef stream_test::stream_driver#(
      .payload_t(payload_t),
      .TA(CyclTime * 0.2),
      .TT(CyclTime * 0.8)
  ) stream_driver_in_t;

  STREAM_DV #(.payload_t(payload_t)) dut_in (.clk_i(clk));
  stream_driver_in_t stream_source = new(dut_in);

  typedef stream_test::stream_driver#(
      .payload_t(payload_t),
      .TA(CyclTime * 0.2),
      .TT(CyclTime * 0.8)
  ) stream_driver_out_t;
  STREAM_DV #(.payload_t(payload_t)) dut_out (.clk_i(clk));
  stream_driver_out_t stream_sink = new(dut_out);


  payload_t current_payload;
  bit data_in_flight = 0;

  assign dut_in.ready = 1'b1;
  stream_deposit #(
      .T(payload_t)
  ) i_stream_deposit (
      .clk_i  (clk),
      .rst_ni (rst_n),
      .valid_i(dut_in.valid),
      .data_i (dut_in.data),
      .data_o (dut_out.data),
      .valid_o(dut_out.valid),
      .ready_i(dut_out.ready)
  );

  initial begin : apply_stimuli
    automatic int unsigned wait_cycl;

    // Disable data stable assertion for this module in the dv interface. The
    // whole point of the stream_deposit is, that the data does not have to be
    // stable.

    $assertoff(0, dut_out);

    @(posedge rst_n);
    stream_source.reset_in();
    for (int i = 0; i < NumReq; i++) begin
      wait_cycl = $urandom_range(0, 5);
      repeat (wait_cycl) @(posedge clk);
      stream_source.send(i);
      current_payload = i;
      data_in_flight = 1;
    end
    $stop();
  end

  initial begin : receive_responses
    automatic payload_t data;
    automatic int unsigned wait_cycl;
    @(posedge rst_n);
    stream_sink.reset_out();
    forever begin
      wait_cycl = $urandom_range(0, 5);
      repeat (wait_cycl) @(posedge clk);
      stream_sink.recv(data);
      assert (data_in_flight) else
        $error("Receieved transaction at output even though the input side did not send any new data.");
      assert (data == current_payload) else
        $error("Received the wrong data. Was %d instead of %d", data, current_payload);
      data_in_flight = 0;
    end
  end

endmodule
