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

module cc_graycode_tb #(
    parameter int Width = 9
);

    logic [Width-1:0] a, b, c, bp = '0;

    cc_binary_to_gray #(Width) dut_ab (a,b);
    cc_gray_to_binary #(Width) dut_bc (b,c);

    task check;
        assert(a == c);
        assert($signed($countones(b) - $countones(bp)) inside {-1,0,1});
        bp = b;
    endtask

    initial begin : p_stim
        logic [Width:0] i;

        // Count up twice, including overflow.
        repeat(2) for (i = 0; i < 2**Width; i++) begin
            a = i;
            #1;
            check();
        end

        // Count backwards.
        for (i = 0; i < 2**Width; i++) begin
            a = Width-i-1;
            #1;
            check();
        end
    end

endmodule
