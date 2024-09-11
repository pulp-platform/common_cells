/// Half of the two-phase clock domain crossing located in the destination
/// domain.

`include "registers.svh"

module cdc_2phase_dst_clearable #(
// tmrg copy start
  parameter type T = logic,
// tmrg copy stop
  parameter int unsigned SYNC_STAGES = 2
)(
  input  logic rst_ni,
  input  logic clk_i,
  input  logic clear_i,
  output T     data_o,
  output logic valid_o,
  input  logic ready_i,
  input  logic async_req_i,
  output logic async_ack_o,
  input  T     async_data_i
);

  (* dont_touch = "true" *)
  (* async_reg = "true" *)
  logic ack_dst_d, ack_dst_q, req_synced, req_synced_q1;
  (* dont_touch = "true" *)
  T data_dst_d, data_dst_q;


  //Synchronize the request
  sync #(
    .STAGES(SYNC_STAGES)
  ) i_sync(
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .serial_i( async_req_i ),
    .serial_o( req_synced  )
  );

  // The ack_dst register changes when a new data item is accepted.
  always_comb begin
    ack_dst_d = ack_dst_q;
    if (clear_i) begin
      ack_dst_d = 1'b0;
    end else if (valid_o && ready_i) begin
      ack_dst_d = ~ack_dst_q;
    end
  end

  // The data_dst register samples when a new data item is presented. This is
  // indicated by a transition in the req_synced line.
  always_comb begin
    data_dst_d = data_dst_q;
    if (req_synced != req_synced_q1 && !valid_o) begin
      data_dst_d = async_data_i;
    end
  end

  // tmrg copy start
  `FFNR(data_dst_q, data_dst_d, clk_i)
  // tmrg copy stop

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ack_dst_q     <= 0;
      req_synced_q1 <= 1'b0;
    end else begin
      ack_dst_q     <= ack_dst_d;
      // The req_synced_q1 is the delayed version of the synchronized req_synced
      // used to detect transitions in the request.
      req_synced_q1 <= req_synced;
    end
  end

  // Output assignments.
  assign valid_o = (ack_dst_q != req_synced_q1);
  assign data_o = data_dst_q;
  assign async_ack_o = ack_dst_q;

endmodule
