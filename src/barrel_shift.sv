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

/// This is a logarithmic barrel shifter for variable shift amounts.
///
/// Example output:
/// * `data_i`:  `16'hABCD`
/// * `shift_i`: `4'h4`
/// * `data_o`:  `16'hBCDA`
module barrel_shift #(
  /// Number of input bytes, if `ByteWidth` is 32'd1 this corresponds to the data width of the
  /// input and output data.
  parameter int unsigned NumInputs = 32'd0,
  /// Control the shift direction.
  ///
  /// `1'b0`: Shift to the left.
  /// `1'b1`: Shift to the right.
  parameter bit ShiftRight = 1'b0,
  /// The width of the sub fields which can be shifted.
  ///
  /// This can also be used to control the shift granularity to something other than 32'd1.
  parameter int unsigned ByteWidth  = 32'd1,
  /// Type definition of a shift sub field (byte).
  ///
  /// Only occurrence of `ByteWidth`.
  parameter type byte_t = logic[ByteWidth-1:0],
  /// Dependent parameter, do **not** overwrite!
  ///
  /// Width of the shift input signal.
  parameter int unsigned ShiftWidth = cf_math_pkg::idx_width(NumInputs),
  /// Dependent parameter, do **not** overwrite!
  ///
  /// Type definition of the shift input signal.
  parameter type shift_t = logic[ShiftWidth-1:0]
) (
  /// The amount the data should be shifted.
  input shift_t shift_i,
  /// Input data to be shifted.
  input byte_t [NumInputs-1:0] data_i,
  /// Output data shifted by `shift_i`.
  output byte_t [NumInputs-1:0] data_o
);

  function int unsigned shift_idx (input int unsigned idx, input int unsigned local_shift);
    // Add `NumInps` to prevent wrong wrapping.
    if (ShiftRight) begin
      return (NumInputs + idx + local_shift) % NumInputs;
    end else begin
      return (NumInputs + idx - local_shift) % NumInputs;
    end
  endfunction

  // intermediate nodes with partial shifted data
  byte_t [ShiftWidth-1:0][NumInputs-1:0] data;

  // generate barrel shifter
  for (genvar lvl = 0; unsigned'(lvl) < ShiftWidth; lvl++) begin : gen_levels
    // local shift
    localparam int unsigned LocalShift = 2**lvl;
    // generate nodes
    for (genvar node = 0; unsigned'(node) < NumInputs; node++) begin : gen_nodes
      // the wrapped index of the previous level
      localparam int unsigned ShiftedIdx = shift_idx(node, LocalShift);
      // connect first level to inputs
      if (lvl == 0) begin : gen_first_level
        assign data[lvl][node] = shift_i[lvl] ? data_i[ShiftedIdx] : data_i[node];
      // internal nodes
      end else begin : gen_internal_level
        assign data[lvl][node] = shift_i[lvl] ? data[lvl-1][ShiftedIdx] : data[lvl-1][node];
      end
    end
  end

  // assign output
  assign data_o = data[ShiftWidth-1];

  // pragma translate_on
    localparam int unsigned OutputWidth = $bits(data_o);
    assert final
      ((ShiftRight &&
          (data_o == OutputWidth'({2{data_i}} >> ($bits(byte_t) * shift_i)))
      ) ||
      (!ShiftRight &&
          (data_o == OutputWidth'(({2{data_i}} << ($bits(byte_t) * shift_i)) >> OutputWidth ))
      ))
    else
      $fatal(1, "Wrong shift output!\nShift:  %d\nInput:  %h\nOutput: %h", shift_i, data_i, data_o);
  // pragma translate_off
endmodule : barrel_shift
