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


/// A register with handshakes that completely cuts any combinational paths
/// between the input and output.
module spill_register #(
  parameter type T      = logic,
  parameter bit  Bypass = 1'b0,     // make this spill register transparent
  parameter bit  EnableFlush = 1'b0 // enable flushing functionality
) (
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic valid_i ,
  input  logic flush_i ,
  output logic ready_o ,
  input  T     data_i  ,
  output logic valid_o ,
  input  logic ready_i ,
  output T     data_o
);

  logic  flush;

  if (EnableFlush) begin : flush_assign_input
    assign flush = flush_i;
  end else begin : flush_assign_zero
    assign flush = 1'b0;
  end

  spill_register_flushable #(
                             .T(T),
                             .Bypass(Bypass)
                             )
  spill_register_i (
                    .clk_i,
                    .rst_ni,
                    .valid_i,
                    .flush_i(flush),
                    .ready_o,
                    .data_i,
                    .valid_o,
                    .ready_i,
                    .data_o
                    );
endmodule
