/// Half of the two-phase clock domain crossing located in the source domain.

`include "registers.svh"

module cdc_2phase_src_clearable #(
// tmrg copy start
  parameter type T = logic,
// tmrg copy stop
  parameter int unsigned SYNC_STAGES = 2
) (
  input  logic rst_ni,
  input  logic clk_i,
  input  logic clear_i,
  input  T     data_i,
  input  logic valid_i,
  output logic ready_o,
  output logic async_req_o,
  input  logic async_ack_i,
  output T     async_data_o
);

  (* dont_touch = "true" *)
  logic  req_src_d, req_src_q, ack_synced;
  (* dont_touch = "true" *)
  logic data_src_d, data_src_q;

  // Synchronize the async ACK
  sync #(
    .STAGES(SYNC_STAGES)
  ) i_sync(
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .serial_i( async_ack_i ),
    .serial_o( ack_synced  )
  );

  // If we receive the clear signal clear the content of the request flip-flop
  // and the data register
  always_comb begin
    data_src_d = data_src_q;
    req_src_d  = req_src_q;
    if (clear_i) begin
      req_src_d  = 1'b0;
    // The req_src and data_src registers change when a new data item is accepted.
    end else if (valid_i && ready_o) begin
      req_src_d  = ~req_src_q;
      data_src_d = data_i;
    end
  end

  // tmrg copy start
  `FFNR(data_src_q, data_src_d, clk_i)
  // tmrg copy stop

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_src_q  <= 0;
    end else begin
      req_src_q  <= req_src_d;
    end
  end

  // Output assignments.
  assign ready_o = (req_src_q == ack_synced);
  assign async_req_o = req_src_q;
  assign async_data_o = data_src_q;

// tmrg copy start
// Assertions
`ifndef COMMON_CELLS_ASSERTS_OFF
  `ifndef SYNTHESIS
  no_clear_and_request: assume property (
     @(posedge clk_i) disable iff(~rst_ni) (clear_i |-> ~valid_i))
    else $fatal(1, "No request allowed while clear_i is asserted.");

  `endif
`endif
// tmrg copy stop

endmodule
