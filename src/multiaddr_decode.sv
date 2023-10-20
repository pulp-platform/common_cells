// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Luca Colagrande <colluca@ethz.ch>

/// Multi-address Decoder: Combinational module which takes an address set
/// in {addr, mask} representation and returns a bit mask `select_o` indicating which
/// address map rules in `addr_map_i` it matches.
///
/// An address set is a set of addresses. The {addr, mask} pair is one possible way of encoding
/// an address set. Asserted bits in the mask indicate that the corresponding bit in addr can
/// be treated as a "don't care", meaning it can assume any value (0 or 1) to produce a valid
/// address in the address set.
///
/// The address map `addr_map_i` is a packed array of rule_t structs. Each rule is itself an
/// address set.
///
/// For each rule the decoder checks if there is an address in the {`addr_i`, `mask_i`} address
/// set which belongs to the address set of the rule. If so, the corresponding bit in `select_o`
/// is set.
/// For each rule, it also returns the subset of addresses in {`addr_i`, `mask_i`} which
/// match the rule {`addr_o[i]`, `mask_o[i]`}.
module multiaddr_decode #(
  /// Highest index which can happen in a rule.
  parameter int unsigned NoIndices = 32'd0,
  /// Total number of rules.
  parameter int unsigned NoRules   = 32'd0,
  /// Address type inside the rules and to decode.
  parameter type         addr_t    = logic,
  /// Rule packed struct type.
  /// The address decoder expects three fields in `rule_t`:
  ///
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   addr_t       addr;
  ///   addr_t       mask;
  /// } rule_t;
  ///
  ///  - `idx`:   index of the rule, has to be < `NoIndices`.
  ///  - `addr`:  any address in the address space described by the rule
  ///  - `mask`:  a bitmask of the same length as the address which transforms the address
  ///             above in a multi-address encoding. A '1' in this mask indicates that the
  ///             corresponding bit in address can take any value and it will still be part
  ///             of this rule's address space.
  ///
  /// {addr, mask} is an alternative representation to the typical interval [start, end)
  /// representation for a collection of addresses. With {addr, mask} we can represent contiguous
  /// intervals of the form [start, end) so long that the latter satisfies the following properties:
  /// - the length of the interval (end - start) is a power of 2 (i.e. 2^N for some integer N)
  /// - the offset of the interval (start) is a multiple of the length
  ///   (i.e. M*2^N for some integer M)
  /// When these properties are satisfied we can go from the [start, end) representation
  /// to the {addr, mask} representation (and viceversa) using the following equations:
  /// - mask =  {'0, {log2(end - start){1'b1}}}
  /// - addr = start
  parameter type         rule_t    = logic
) (
  /// Multi-address to decode.
  input  addr_t                 addr_i,
  input  addr_t                 mask_i,
  /// Address map.
  input  rule_t [NoRules-1:0]   addr_map_i,
  /// Decoded indices.
  output logic  [NoIndices-1:0] select_o,
  /// Decoded multi-address.
  output addr_t [NoIndices-1:0] addr_o,
  output addr_t [NoIndices-1:0] mask_o,
  /// Decode is valid.
  output logic                  dec_valid_o,
  /// Decode is not valid, no matching rule found.
  output logic                  dec_error_o
);

  logic [NoRules-1:0] matched_rules; // purely for address map debugging

  always_comb begin
    // default assignments
    matched_rules = '0;
    dec_valid_o   = 1'b0;
    dec_error_o   = 1'b1;
    select_o      = '0;
    addr_o        = '0;
    mask_o        = '0;

    // Match the rules
    for (int unsigned i = 0; i < NoRules; i++) begin
      automatic int unsigned idx = addr_map_i[i].idx;
      // We have a match if at least one address of the input
      // address set is a part of the rule's address set.
      // We have this condition when all bits in the input address match
      // all bits in `addr_map_i[i].addr`, with possible exception
      // of those bits which are either masked in the input address
      // or in the addrmap rule. In other words, any bit which is masked
      // either in the input address or in the addrmap rule is treated as a don't care
      automatic addr_t dont_care = mask_i | addr_map_i[i].mask;
      automatic addr_t matching_bits = ~(addr_i ^ addr_map_i[i].addr);
      automatic logic match = &(dont_care | matching_bits);
      if (match) begin
        matched_rules[i] = 1'b1;
        dec_valid_o      = 1'b1;
        dec_error_o      = 1'b0;
        select_o[idx]   |= 1'b1;
        // When there is a partial match, i.e. only a subset of the input address set
        // falls in the address set of the rule, we want to return this subset
        // {addr_o, mask_o}.
        // Bits which are masked in the input address but not in the addrmap rule
        // are resolved to the value in the addrmap, and are thus unmasked in the
        // output address set. All other bits remain masked or unchanged.
        mask_o[idx] = mask_i & addr_map_i[i].mask;
        addr_o[idx] = (~mask_i & addr_i) | (mask_i & addr_map_i[i].addr);
      end
    end
  end

  // Assumptions and assertions
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ifndef XSIM
  // synopsys translate_off
  initial begin : proc_check_parameters
    assume (NoRules > 0) else
      $fatal(1, $sformatf("At least one rule needed"));
    assume ($bits(addr_i) == $bits(addr_map_i[0].addr)) else
      $warning($sformatf("Input address has %d bits and address map has %d bits.",
        $bits(addr_i), $bits(addr_map_i[0].addr)));
  end

  // These following assumptions check the validity of the address map.
  // check_idx: Enforces a valid index in the rule.
  always @(addr_map_i) #0 begin : proc_check_addr_map
    if (!$isunknown(addr_map_i)) begin
      for (int unsigned i = 0; i < NoRules; i++) begin
        // check the SLV ids
        check_idx : assume (addr_map_i[i].idx < NoIndices) else
            $fatal(1, $sformatf("This rule has a IDX that is not allowed!!!\n\
            Violating rule %d.\n\
            Rule> IDX: %h\n\
            Rule> MAX_IDX: %h\n\
            #####################################################",
            i, addr_map_i[i].idx, (NoIndices-1)));
      end
    end
  end

  // synopsys translate_on
  `endif
  `endif
endmodule
