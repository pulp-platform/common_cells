// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Backwards compatibility layer for the FIFO. Deprecated.
module generic_fifo #(
  parameter int unsigned DATA_WIDTH = 32,
  parameter int unsigned DATA_DEPTH = 8
)(
  input  logic                  clk,
  input  logic                  rst_n,
  //PUSH SIDE
  input  logic [DATA_WIDTH-1:0] data_i,
  input  logic                  valid_i,
  output logic                  grant_o,
  //POP SIDE
  output logic [DATA_WIDTH-1:0] data_o,
  output logic                  valid_o,
  input  logic                  grant_i,

  input  logic                  test_mode_i
);

  logic full, empty;
  assign grant_o = ~full;
  assign valid_o = ~empty;

  fifo_v2 #(
    .DATA_WIDTH ( DATA_WIDTH ),
    .DEPTH      ( DATA_DEPTH )
  ) i_fifo (
    .clk_i       ( clk          ),
    .rst_ni      ( rst_n        ),
    .flush_i     ( 1'b0         ),
    .testmode_i  ( test_mode_i  ),
    .full_o      ( full         ),
    .empty_o     ( empty        ),
    .alm_full_o  (              ),
    .alm_empty_o (              ),
    .data_i      ( data_i       ),
    .push_i      ( valid_i      ),
    .data_o      ( data_o       ),
    .pop_i       ( grant_i      )
  );

endmodule
