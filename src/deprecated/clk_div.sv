// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba
// Description: Divides the clock by an integer factor
module clk_div #(
    parameter int unsigned RATIO = 4,
    parameter bit SHOW_WARNING = 1'b1
)(
    input  logic clk_i,      // Clock
    input  logic rst_ni,     // Asynchronous reset active low
    input  logic testmode_i, // testmode
    input  logic en_i,       // enable clock divider
    output logic clk_o       // divided clock out
);
    logic [RATIO-1:0] counter_q;
    logic clk_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            clk_q       <= 1'b0;
            counter_q <= '0;
        end else begin
            clk_q <= 1'b0;
            if (en_i) begin
                if (counter_q == (RATIO[RATIO-1:0] - 1)) begin
                    clk_q <= 1'b1;
                end else begin
                    counter_q <= counter_q + 1;
                end
            end
        end
    end
    // output assignment - bypass in testmode
    assign clk_o = testmode_i ? clk_i : clk_q;

  if (SHOW_WARNING) begin : gen_elab_warning
    $warning(
       "This clock divider is deprecated and not reccomended since  ",
       "the generated output clock has a very unbalanced duty cycle  ",
       "(1/RATIO). For new designs we reccomend using the at-runtime ",
       "configurable clk_int_div module which always generates 50%%  ",
       "duty cycle clock. If you don't need at runtime configuration ",
       "support, you can instantiate clk_int_div as follows to       ",
       "obtain a module with roughly the same behavior (except for   ",
       "the 50 %% duty cycle):\n                                     ",
       "\n                                                           ",
       "  clk_int_div #(\n                                           ",
       "    .DIV_VALUE_WIDTH($clog2(RATIO+1)),\n                     ",
       "    .DEFAULT_DIV_VALUE(RATIO)\n                              ",
       "  ) i_clk_int_div(\n                                         ",
       "    .clk_i,\n                                                ",
       "    .rst_ni,\n                                               ",
       "    .test_mode_en_i(testmode_i),\n                           ",
       "    .en_i,\n                                                 ",
       "    .div_i('1), // Ignored, used default value\n             ",
       "    .div_valid_i(1'b0),\n                                    ",
       "    .div_ready_o(),\n                                        ",
       "    .clk_o\n                                                 ",
       "  );                                                         ",
       "\n                                                           ",
       "If you know what your are doing and want to disable this     ",
       "warning message, you can disable it by overriding the new    ",
       "optional clk_div parameter SHOW_WARNING to 1'b0.");
  end

endmodule
