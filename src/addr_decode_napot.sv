// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>

/// This module wraps `addr_decode` in its naturally-aligned power of two (NAPOT) variant,
/// alleviating the need to set the `Napot` parameter and using more descriptive `rule_t`
/// field names. See the `addr_decode`documentation for details.
module addr_decode_napot #(
  /// Highest index which can happen in a rule.
  parameter int unsigned NoIndices = 32'd0,
  /// Total number of rules.
  parameter int unsigned NoRules   = 32'd0,
  /// Address type inside the rules and to decode.
  parameter type         addr_t    = logic,
  /// Rule packed struct type.
  /// The NAPOT address decoder expects three fields in `rule_t`:
  ///
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   addr_t       base;
  ///   addr_t       mask;
  /// } rule_t;
  ///
  ///  - `idx`:   index of the rule, has to be < `NoIndices`.
  ///  - `base`:  base address whose specified bits should match `addr_i`.
  ///  - `mask`:  set for bits which are to be checked to determine a match.
  parameter type         rule_t    = logic,
  /// Dependent parameter, do **not** overwite!
  ///
  /// Width of the `idx_o` output port.
  parameter int unsigned IdxWidth  = cf_math_pkg::idx_width(NoIndices),
  /// Dependent parameter, do **not** overwite!
  ///
  /// Type of the `idx_o` output port.
  parameter type         idx_t     = logic [IdxWidth-1:0]
) (
  /// Address to decode.
  input  addr_t               addr_i,
  /// Address map: rule with the highest array position wins on collision
  input  rule_t [NoRules-1:0] addr_map_i,
  /// Decoded index.
  output idx_t                idx_o,
  /// Decode is valid.
  output logic                dec_valid_o,
  /// Decode is not valid, no matching rule found.
  output logic                dec_error_o,
  /// Enable default port mapping.
  ///
  /// When not used, tie to `0`.
  input  logic                en_default_idx_i,
  /// Default port index.
  ///
  /// When `en_default_idx_i` is `1`, this will be the index when no rule matches.
  ///
  /// When not used, tie to `0`.
  input  idx_t                default_idx_i
);

  // Rename struct field names to those expected by `addr_decode`
  typedef struct packed {
    int unsigned  idx;
    addr_t        start_addr;
    addr_t        end_addr;
  } rule_range_t;

  addr_decode #(
    .NoIndices ( NoIndices    ) ,
    .NoRules   ( NoRules      ),
    .addr_t    ( addr_t       ),
    .rule_t    ( rule_range_t ),
    .Napot     ( 1            )
  ) i_addr_decode (
    .addr_i,
    .addr_map_i,
    .idx_o,
    .dec_valid_o,
    .dec_error_o,
    .en_default_idx_i,
    .default_idx_i
);

endmodule
