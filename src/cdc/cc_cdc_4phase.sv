// Copyright 2018 ETH Zurich and University of Bologna.
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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A four-phase clock domain crossing.
///
/// CONSTRAINT: Requires max_delay of min_period(src_clk_i, dst_clk_i) through
/// the paths async_req, async_ack, async_data.
/* verilator lint_off DECLFILENAME */
module cc_cdc_4phase #(
  parameter type T = logic,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int SYNC_STAGES = 2
) (
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,

  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i
);

  // Asynchronous handshake signals.
  (* dont_touch = "true" *) logic async_req;
  (* dont_touch = "true" *) logic async_ack;
  (* dont_touch = "true" *) T async_data;

  // The sender in the source domain.
  cc_cdc_4phase_src #(
    .T            ( T           ),
    .SYNC_STAGES  ( SYNC_STAGES )
  ) i_src (
    .rst_ni       ( src_rst_ni  ),
    .clk_i        ( src_clk_i   ),
    .data_i       ( src_data_i  ),
    .valid_i      ( src_valid_i ),
    .ready_o      ( src_ready_o ),
    .async_req_o  ( async_req   ),
    .async_ack_i  ( async_ack   ),
    .async_data_o ( async_data  )
  );

  // The receiver in the destination domain.
  cc_cdc_4phase_dst #(
    .T            ( T           ),
    .SYNC_STAGES  ( SYNC_STAGES )
  ) i_dst (
    .rst_ni       ( dst_rst_ni  ),
    .clk_i        ( dst_clk_i   ),
    .data_o       ( dst_data_o  ),
    .valid_o      ( dst_valid_o ),
    .ready_i      ( dst_ready_i ),
    .async_req_i  ( async_req   ),
    .async_ack_o  ( async_ack   ),
    .async_data_i ( async_data  )
  );

endmodule


/// Half of the two-phase clock domain crossing located in the source domain.
module cc_cdc_4phase_src #(
  parameter type T = logic,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int SYNC_STAGES = 2
) (
  input  logic rst_ni,
  input  logic clk_i,
  input  T     data_i,
  input  logic valid_i,
  output logic ready_o,
  output logic async_req_o,
  input  logic async_ack_i,
  output T     async_data_o
);

  (* dont_touch = "true" *)
  logic req_src_q, ack;
  (* dont_touch = "true" *)
  T data_src_q;

  // The req_src and data_src registers change when a new data item is accepted.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_src_q  <= 0;
      data_src_q <= '0;
    end else if (valid_i && ready_o) begin
      req_src_q  <= ~req_src_q;
      data_src_q <= data_i;
    end
  end

  cc_sync #(.STAGES(SYNC_STAGES)) i_cc_sync (
    .clk_i,
    .rst_ni,
    .serial_i ( async_ack_i ),
    .serial_o ( ack         )
  );


  // Output assignments.
  assign ready_o = (req_src_q == ack);
  assign async_req_o = req_src_q;
  assign async_data_o = data_src_q;

endmodule


/// Half of the two-phase clock domain crossing located in the destination
/// domain.
module cc_cdc_4phase_dst #(
  parameter type T = logic,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int SYNC_STAGES = 2
) (
  input  logic rst_ni,
  input  logic clk_i,
  output T     data_o,
  output logic valid_o,
  input  logic ready_i,
  input  logic async_req_i,
  output logic async_ack_o,
  input  T     async_data_i
);

  (* dont_touch = "true" *)
  (* async_reg = "true" *)
  logic req_q0, req_q1, ack_dst_q;
  (* dont_touch = "true" *)
  T data_dst_q;

  // The ack_dst register changes when a new data item is accepted.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ack_dst_q  <= 0;
    end else if (valid_o && ready_i) begin
      ack_dst_q  <= ~ack_dst_q;
    end
  end

  // The data_dst register changes when a new data item is presented. This is
  // indicated by the async_req line changing levels.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_dst_q <= '0;
    end else if (req_q0 != req_q1 && !valid_o) begin
      data_dst_q <= async_data_i;
    end
  end

  // The req_dst and req registers act as synchronization stages.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_q1    <= 0;
    end else begin
      req_q1    <= req_q0;
    end
  end

  cc_sync #(.STAGES(SYNC_STAGES)) i_cc_sync (
    .clk_i,
    .rst_ni,
    .serial_i ( async_req_i ),
    .serial_o ( req_q0      )
  );

  // Output assignments.
  assign valid_o = (ack_dst_q != req_q1);
  assign data_o = data_dst_q;
  assign async_ack_o = ack_dst_q;

endmodule
/* verilator lint_on DECLFILENAME */
