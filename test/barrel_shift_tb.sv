// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// Thomas Benz <tbenz@iis.ee.ethz.ch>
// Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Testbench for the module `barrel_shift`.
///
/// Golden model is an assertion inside of `barrel_shift`.
module barrel_shift_tb #(
  /// Number of input bytes.
  parameter int unsigned TbNumInputs = 32'd8,
  /// Do right shifts.
  parameter bit TbShiftRight = 1'b0,
  /// Width of a byte.
  parameter int unsigned TbByteWidth = 32'd1,
  /// Number of test cases.
  parameter int unsigned TbNumTests = 32'd10000
);

  localparam int unsigned ShiftWidth = cf_math_pkg::idx_width(TbNumInputs);
  typedef logic [TbByteWidth-1:0] byte_t;
  typedef logic [ShiftWidth-1:0]  shift_t;

  shift_t                   shift;
  byte_t  [TbNumInputs-1:0] inp;
  byte_t  [TbNumInputs-1:0] oup;

  initial begin
    inp   = '0;
    shift = '0;

    for (int unsigned i_test = 0; i_test < TbNumTests; i_test++) begin
      #1;
      shift = shift_t'($urandom_range(0, TbNumInputs-1));
      for (int unsigned i_byte = 0; i_byte < TbNumInputs; i_byte++) begin
        inp[i_byte] = byte_t'($urandom());
      end
      #0;
      $display("Shift: %d Inp: %h Oup: %h", shift, inp, oup);
    end
    #20;
    $display("Simulation end reached.",);
    $stop();
  end

  barrel_shift #(
    .NumInputs ( TbNumInputs  ),
    .ShiftRight( TbShiftRight ),
    .byte_t    ( byte_t       )
  ) i_log_barrel_shifter (
    .shift_i ( shift ),
    .data_i  ( inp   ),
    .data_o  ( oup   )
  );

endmodule : barrel_shift_tb
