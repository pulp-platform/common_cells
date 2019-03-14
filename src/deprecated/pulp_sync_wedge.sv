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

module pulp_sync_wedge 
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_i,
    input  logic serial_i,
    output logic r_edge_o,
    output logic f_edge_o,
    output logic serial_o
);
    logic       clk_int;
    logic       serial_int;
   
    logic r_bf_synch;

    
    always_ff @(posedge clk_int, negedge rstn_i)
    begin
         if (!rstn_i)
         begin
             r_bf_synch <= 1'b0;
         end
         else
         begin
             r_bf_synch <= serial_int;
         end
    end
    
    assign serial_o =  r_bf_synch;

    assign f_edge_o = !serial_int &  r_bf_synch;
    assign r_edge_o =  serial_int & !r_bf_synch;
   


    pulp_sync #( .STAGES(2) )  r_bf_synch_1_2
    (
        .clk_i    ( clk_int     ),
        .rstn_i   ( rstn_i      ),
        .serial_i ( serial_i    ),
        .serial_o ( serial_int  )
    );

    pulp_clock_gating i_clk_gate
    (
        .clk_i    ( clk_i     ),
        .en_i     ( en_i      ),
        .test_en_i( 1'b0      ),
        .clk_o    ( clk_int   )
    );

endmodule
