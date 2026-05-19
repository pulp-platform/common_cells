// Copyright 2026 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Philippe Sauter <phsauter@iis.ee.ethz.ch>
//
// Description: Composed Reset-Controller Properties
// Instantiate the bidirectional reset controller with a one-cycle local
// acknowledgement model and prove cross-domain clear/isolate sequencing.

module cc_cdc_reset_ctrlr_composed_harness (
  input wire a_clk_i,
  input wire a_rst_ni,
  input wire a_clear_i,
  input wire b_clk_i,
  input wire b_rst_ni,
  input wire b_clear_i
);

  logic a_clear_o;
  logic a_clear_ack_q;
  logic a_isolate_o;
  logic a_isolate_ack_q;
  logic b_clear_o;
  logic b_clear_ack_q;
  logic b_isolate_o;
  logic b_isolate_ack_q;

  logic a_init_q = 1'b0;
  logic b_init_q = 1'b0;

  cc_cdc_reset_ctrlr #(
    .SyncStages        ( 2    ),
    .ClearOnAsyncReset ( 1'b1 )
  ) i_dut (
    .a_clk_i,
    .a_rst_ni,
    .a_clear_i,
    .a_clear_o,
    .a_clear_ack_i   ( a_clear_ack_q   ),
    .a_isolate_o,
    .a_isolate_ack_i ( a_isolate_ack_q ),
    .b_clk_i,
    .b_rst_ni,
    .b_clear_i,
    .b_clear_o,
    .b_clear_ack_i   ( b_clear_ack_q   ),
    .b_isolate_o,
    .b_isolate_ack_i ( b_isolate_ack_q )
  );

  always_ff @(posedge a_clk_i) begin
    a_init_q <= 1'b1;
    if (!a_init_q) begin
      assume (!a_rst_ni);
    end
  end

  always_ff @(posedge b_clk_i) begin
    b_init_q <= 1'b1;
    if (!b_init_q) begin
      assume (!b_rst_ni);
    end
  end

  always_comb begin
    if (a_init_q) begin
      assume (a_rst_ni);
    end else begin
      assume (!a_clear_i);
    end

    if (b_init_q) begin
      assume (b_rst_ni);
    end else begin
      assume (!b_clear_i);
    end
  end

  always_ff @(posedge a_clk_i, negedge a_rst_ni) begin
    if (!a_rst_ni) begin
      a_isolate_ack_q <= 1'b0;
      a_clear_ack_q   <= 1'b0;
    end else begin
      a_isolate_ack_q <= a_isolate_o;
      a_clear_ack_q   <= a_clear_o;
    end
  end

  always_ff @(posedge b_clk_i, negedge b_rst_ni) begin
    if (!b_rst_ni) begin
      b_isolate_ack_q <= 1'b0;
      b_clear_ack_q   <= 1'b0;
    end else begin
      b_isolate_ack_q <= b_isolate_o;
      b_clear_ack_q   <= b_clear_o;
    end
  end

  always_comb begin
    if (a_rst_ni) begin
      assert (!a_clear_o || a_isolate_o);
    end

    if (b_rst_ni) begin
      assert (!b_clear_o || b_isolate_o);
    end

    if (a_rst_ni && b_rst_ni) begin
      assert (!(a_clear_o || b_clear_o) || (a_isolate_o && b_isolate_o));
    end
  end

  always_ff @(posedge a_clk_i) begin
    if (a_rst_ni && $past(a_rst_ni) && a_init_q) begin
      assert (a_isolate_ack_q == $past(a_isolate_o));
      assert (a_clear_ack_q == $past(a_clear_o));
    end

    cover (a_rst_ni && b_rst_ni && a_clear_o && b_isolate_o);
  end

  always_ff @(posedge b_clk_i) begin
    if (b_rst_ni && $past(b_rst_ni) && b_init_q) begin
      assert (b_isolate_ack_q == $past(b_isolate_o));
      assert (b_clear_ack_q == $past(b_clear_o));
    end

    cover (a_rst_ni && b_rst_ni && b_clear_o && a_isolate_o);
  end

endmodule
