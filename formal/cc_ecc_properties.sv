// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Warren Smith <233830950+repowazdogz-droid@users.noreply.github.com>

// Property checker for the cc_ecc_encode / cc_ecc_decode pair.
//
// The four cases below are the rows of the truth table documented in the
// header of cc_ecc_decode.sv. Each row gets its own decoder instance in
// cc_ecc_formal.sv, so no precondition can weaken another row.
//
// What these properties do NOT establish:
//   - nothing is asserted about data_o under a double error. The decoder does
//     not promise a value there, and the syndrome can address a position
//     outside the codeword, in which case no correction is applied at all.
//   - only nonzeroness, not an exact value, is asserted about the syndrome
//     under a double error. The documented contract promises a non-zero
//     syndrome there and nothing more.
//   - nothing is claimed for more than two flipped bits, which is beyond the
//     distance of a SECDED code.
//   - the encoder is exercised only through this decoder, not against an
//     independent implementation of the same code, so this is a matched-pair
//     proof rather than an interoperability one.
module cc_ecc_properties #(
    parameter  int unsigned DataWidth   = 32,
    localparam int unsigned ParityWidth = cc_pkg::ecc_get_parity_width(DataWidth),
    localparam int unsigned CwWidth     = cc_pkg::ecc_get_cw_width(DataWidth),
    /// Encoded word: the Hamming codeword plus the extended parity bit.
    localparam int unsigned TotWidth    = CwWidth + 1,
    localparam int unsigned IdxWidth    = cc_pkg::idx_width(TotWidth)
) (
    /// Word presented to the encoder.
    input logic [DataWidth-1:0] data_i,
    /// Symbolic positions of the injected bit flips, indexing the encoded word.
    input logic [IdxWidth-1:0]  pos_a_i,
    input logic [IdxWidth-1:0]  pos_b_i,

    /// Decoder fed the untouched encoded word.
    input logic [DataWidth-1:0] clean_data_i,
    input logic                 clean_single_i,
    input logic                 clean_parity_i,
    input logic                 clean_double_i,
    input logic [ParityWidth-1:0] clean_syndrome_i,

    /// Decoder fed one flipped bit inside the Hamming codeword.
    input logic [DataWidth-1:0] sgl_data_i,
    input logic                 sgl_single_i,
    input logic                 sgl_parity_i,
    input logic                 sgl_double_i,
    input logic [ParityWidth-1:0] sgl_syndrome_i,

    /// Decoder fed a flipped extended parity bit, codeword untouched.
    input logic [DataWidth-1:0] par_data_i,
    input logic                 par_single_i,
    input logic                 par_parity_i,
    input logic                 par_double_i,
    input logic [ParityWidth-1:0] par_syndrome_i,

    /// Decoder fed two distinct flipped bits anywhere in the encoded word.
    input logic                 dbl_single_i,
    input logic                 dbl_parity_i,
    input logic                 dbl_double_i,
    input logic [ParityWidth-1:0] dbl_syndrome_i
);

  // ---------------------------------------------------------------------
  // Parity-width anchor
  //
  // cc_ecc_encode places a Hamming parity bit at every 1-based codeword
  // position that is a power of two and a data bit everywhere else. That
  // layout is only consistent if the codeword contains exactly ParityWidth
  // power-of-two positions and exactly DataWidth others.
  //
  // Counting those positions is independent of how cc_pkg::ecc_get_parity_width
  // arrives at its answer, so a defect in the package search is not reproduced
  // by the check meant to catch it. Recomputing the same search here would
  // agree with the package for the same wrong reason.
  //
  // Both operands are elaboration-time constants. This is therefore an
  // elaboration check, not one of the proof obligations below, and it is not
  // counted among the proved properties.
  function automatic int unsigned count_parity_positions(input int unsigned cw_width);
    count_parity_positions = 0;
    for (int unsigned i = 1; i <= cw_width; i++) begin
      if (cc_pkg::is_power_of_2(i)) count_parity_positions++;
    end
  endfunction

  localparam int unsigned CountedParityPositions = count_parity_positions(CwWidth);

  if (CountedParityPositions != ParityWidth) begin : gen_parity_width_mismatch
    $error("cc_ecc: codeword of %0d bits holds %0d parity positions, but cc_pkg reports %0d",
           CwWidth, CountedParityPositions, ParityWidth);
  end
  if (CwWidth - CountedParityPositions != DataWidth) begin : gen_data_width_mismatch
    $error("cc_ecc: codeword of %0d bits leaves %0d data positions for DataWidth %0d",
           CwWidth, CwWidth - CountedParityPositions, DataWidth);
  end

  // ---------------------------------------------------------------------
  // Both flip positions must address a bit of the encoded word. Without this
  // the solver is free to pick an index that addresses nothing, the injected
  // error becomes a no-op, and P2 and P4 pass for the wrong reason.
  //
  // The comparison is made at 32 bits and not cast down to IdxWidth. When
  // TotWidth is exactly a power of two, IdxWidth'(TotWidth) truncates to zero,
  // the assumption becomes unsatisfiable, and every property below is
  // vacuously true. The `cover` task exists to keep that class of mistake
  // visible; see formal/README.md.
  always_comb begin
    assume (32'(pos_a_i) < TotWidth);
    assume (32'(pos_b_i) < TotWidth);
  end

  // ---------------------------------------------------------------- P1
  // No corruption: the data returns intact and no flag is raised.
  always_comb begin
    p1_data:     assert (clean_data_i == data_i);
    p1_single:   assert (clean_single_i == 1'b0);
    p1_parity:   assert (clean_parity_i == 1'b0);
    p1_double:   assert (clean_double_i == 1'b0);
    p1_syndrome: assert (clean_syndrome_i == '0);
  end

  // ---------------------------------------------------------------- P2
  // Exactly one flipped bit inside the Hamming codeword, either a data bit or
  // a Hamming parity bit: corrected, and reported as a single error.
  //
  // The precondition excludes the extended parity bit on purpose. A flip there
  // is reported through parity_error_o, so stating P2 over the whole encoded
  // word would contradict the documented truth table.
  always_comb begin
    if (32'(pos_a_i) < CwWidth) begin
      p2_data:   assert (sgl_data_i == data_i);
      p2_single: assert (sgl_single_i == 1'b1);
      p2_parity: assert (sgl_parity_i == 1'b0);
      p2_double: assert (sgl_double_i == 1'b0);
      // The syndrome is the 1-based position of the flipped codeword bit:
      // flipping bit k toggles exactly the syndrome bits set in (k + 1).
      // The comparison is made at 32 bits for the same truncation reason as
      // the position assumptions above.
      p2_syndrome: assert (32'(sgl_syndrome_i) == 32'(pos_a_i) + 1);
    end
  end

  // ---------------------------------------------------------------- P3
  // Only the extended parity bit is flipped: the data is untouched and the
  // error is reported as a parity error.
  always_comb begin
    p3_data:     assert (par_data_i == data_i);
    p3_parity:   assert (par_parity_i == 1'b1);
    p3_single:   assert (par_single_i == 1'b0);
    p3_double:   assert (par_double_i == 1'b0);
    // The syndrome only covers the Hamming codeword, so a flip of the
    // extended parity bit alone leaves it zero.
    p3_syndrome: assert (par_syndrome_i == '0);
  end

  // ---------------------------------------------------------------- P4
  // Two distinct flipped bits anywhere in the encoded word, the extended
  // parity bit included: reported as an uncorrectable double error.
  always_comb begin
    if (pos_a_i != pos_b_i) begin
      p4_double: assert (dbl_double_i == 1'b1);
      p4_single: assert (dbl_single_i == 1'b0);
      p4_parity: assert (dbl_parity_i == 1'b0);
      // Only nonzeroness is claimed here: the documented contract promises a
      // non-zero syndrome for a double fault, but no particular value, so the
      // exact (implementation-determined) value is deliberately not asserted.
      p4_syndrome: assert (dbl_syndrome_i != '0);
    end
  end

  // ------------------------------------------------------------- coverage
  // A property whose precondition is unreachable is not evidence. These cover
  // points show that the injected-error cases are attainable at the low and
  // high ends of the encoded word, that the extended parity bit is reachable
  // on its own, and that representative two-bit combinations exist.
  always_comb begin
    c_sgl_low:  cover (32'(pos_a_i) == 32'd0);
    c_sgl_high: cover (32'(pos_a_i) == CwWidth - 1);
    c_par_only: cover (32'(pos_a_i) == CwWidth);
    c_dbl_span: cover (32'(pos_a_i) == 32'd0 && 32'(pos_b_i) == CwWidth);
    c_dbl_adj:  cover (32'(pos_a_i) == 32'd0 && 32'(pos_b_i) == 32'd1);
  end

endmodule : cc_ecc_properties
