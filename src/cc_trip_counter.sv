// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Colagrande <colluca@iis.ee.ethz.ch>
//
// Counter which resets automatically after it reaches a specified bound, i.e.
// when it "trips". Useful e.g. for implementing hardware loop logic, where the
// counter can be used to track the induction variable of a loop.
//
// Example use case
// ================
//
// Set `delta_i` to `j_incr` and `bound_i` to `j_bound`, and `q_o` will
// track `j` in the following loop nest:
//
//   for (int i = 0; i <= i_bound; i+=i_incr)
//     for (int j = 0; j <= j_bound; j+=j_incr)
//
// Step the `j` loop iterations by asserting `en_i` for each iteration.
// The `last_o` flag is asserted when the last iteration of the `j` loop is
// reached.
// The `trip_o` flag is asserted when stepping the loop during the last
// iteration, after which the counter is reset.
//
// Caveats
// =======
//
// To reduce ambiguity and complexity, we require the counter to land exactly
// on the bound on the last iteration. This ensures there exists an injective
// function between increment and bound inputs and the output induction
// variable sequence. For example, the {0 2 4 6} sequence could be obtained by
// setting `j_incr` to 2 and `j_bound` to either 6 or 7. With this constraint,
// only the prior is valid, and the latter will trigger the
// `CounterExceedsBound` assertion.
//
// To track the induction variable of a loop with increment `incr` and `N`
// iterations, set `delta_i` to `incr` and `bound_i` to `(N-1)*incr`.

`include "common_cells/assertions.svh"

module cc_trip_counter #(
    parameter int unsigned Width = 4
)(
    input  logic             clk_i,   // Clock
    input  logic             rst_ni,  // Asynchronous reset active low
    input  logic             clr_i,   // Synchronous clear active high
    input  logic             en_i,
    input  logic [Width-1:0] delta_i,
    input  logic [Width-1:0] bound_i,
    output logic [Width-1:0] q_o,
    output logic             last_o,
    output logic             trip_o
);

    cc_delta_counter #(
        .Width(Width)
    ) i_delta_counter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .clr_i(clr_i || trip_o),
        .en_i(en_i),
        .load_i(1'b0),
        .down_i(1'b0),
        .delta_i(delta_i),
        .d_i('0),
        .q_o(q_o),
        .overflow_o()
    );

    assign last_o = (q_o == bound_i);
    assign trip_o = last_o && en_i;

    // Only flag a real overshoot, i.e. incrementing past `bound_i` without landing on it exactly.
    // On the trip cycle itself (`last_o`), `q_o` already equals `bound_i` and `en_i` is expected to
    // be high, so `q_o + delta_i` legitimately exceeds `bound_i` there without indicating a bug.
    // We also exclude cycles where `clr_i` is asserted, and zero-extend the addends before summing
    // them, since `q_o`, `delta_i` and `bound_i` share the same width and could otherwise overflow
    // back to a value below `bound_i`, masking a real overrun.
    `ASSERT(CounterExceedsBound, !(en_i && !last_o && !clr_i &&
      ({1'b0, q_o} + {1'b0, delta_i}) > {1'b0, bound_i}))

endmodule
