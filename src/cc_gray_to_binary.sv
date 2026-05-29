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

/// A gray code to binary converter.
module cc_gray_to_binary #(
    parameter int unsigned N = 1
)(
    input  logic [N-1:0] a_i,
    output logic [N-1:0] z_o
);
    for (genvar i = 0; i < N; i++)
        assign z_o[i] = ^a_i[N-1:i];
endmodule
