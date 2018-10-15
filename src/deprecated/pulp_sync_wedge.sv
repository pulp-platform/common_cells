// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Antonio Pullini <pullinia@iis.ee.ethz.ch>

module pulp_sync_wedge (
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_i,
    input  logic serial_i,
    output logic r_edge_o,
    output logic f_edge_o,
    output logic serial_o
);
   
    logic [2:0] r_reg;
    logic [2:0] r_next;
    
    always_ff @(posedge clk_i, negedge rstn_i) begin
         if (!rstn_i) begin
             r_reg <= 3'h0;
         end else begin
             if (en_i) begin
                 r_reg <= {serial_i, r_reg[2:1]};
             end
         end
      end
    
    assign serial_o =  r_reg[0];
    assign f_edge_o = !r_reg[1] &  r_reg[0];
    assign r_edge_o =  r_reg[1] & !r_reg[0];
   
endmodule
