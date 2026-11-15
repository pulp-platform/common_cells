// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Georg Rutishauser <georgr@iis.ee.ethz.ch>

module stream_fifo #(
    /// FIFO is in fall-through mode
    parameter bit          FALL_THROUGH = 1'b0,
    /// Default data width if the fifo is of type logic
    parameter int unsigned DATA_WIDTH   = 32,
    /// Depth can be arbitrary from 0 to 2**32
    parameter int unsigned DEPTH        = 8,
    parameter type         T            = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1
) (
    input  logic                  clk_i,      // Clock
    input  logic                  rst_ni,     // Asynchronous reset active low
    input  logic                  flush_i,    // flush the fifo
    input  logic                  testmode_i, // test_mode to bypass clock gating
    output logic [ADDR_DEPTH-1:0] usage_o,    // fill pointer
    // input interface
    input  T                      data_i,     // data to push into the fifo
    input  logic                  valid_i,    // input data valid
    output logic                  ready_o,    // fifo is not full
    // output interface
    output T                      data_o,     // output data
    output logic                  valid_o,    // fifo is not empty
    input  logic                  ready_i,    // pop head from fifo
    // fault indication: rel_fifo internal TMR fault or ECC error on the popped word
    output logic                  fifo_fault_o
);

    logic push, pop;
    logic empty, full;

    assign push    = valid_i & ~full;
    assign pop     = ready_i & ~empty;
    assign ready_o = ~full;
    assign valid_o = ~empty;

    // The FIFO storage is protected by a Hsiao SECDED code: the data is encoded
    // before it enters rel_fifo and decoded (and corrected) after it leaves.
    localparam int unsigned DataW    = $bits(T);
    localparam int unsigned ProtW    = hsiao_ecc_pkg::min_ecc(DataW);
    localparam int unsigned EccDataW = DataW + ProtW;

    logic [DataW-1:0]    data_raw_in, data_raw_out;
    logic [EccDataW-1:0] data_enc, data_enc_out;
    logic [1:0]          ecc_err;
    logic                rel_fifo_fault;

    // Simulation only: unused bits of the payload (e.g. rs2 of an FP convert)
    // may arrive as X. One X bit would poison the whole Hsiao codeword (syndrome
    // becomes X, so the decoder output is all X). Replace X bits by 0 before
    // encoding. In silicon these bits are plain 0/1, so nothing is needed.
`ifndef TARGET_SYNTHESIS
    always_comb begin
      logic [DataW-1:0] data_in_vec;
      data_in_vec = data_i;
      for (int unsigned b = 0; b < DataW; b++) begin
        data_raw_in[b] = $isunknown(data_in_vec[b]) ? 1'b0 : data_in_vec[b];
      end
    end
`else
    assign data_raw_in = data_i;
`endif

    hsiao_ecc_enc #(
        .DataWidth ( DataW ),
        .ProtWidth ( ProtW )
    ) i_ecc_enc (
        .in  ( data_raw_in ),
        .out ( data_enc    )
    );

    rel_fifo #(
        .FallThrough ( FALL_THROUGH ),
        .DataWidth   ( EccDataW     ),
        .Depth       ( DEPTH        )
    ) i_rel_fifo (
        .clk_i,
        .rst_ni,
        .flush_i,
        .testmode_i,
        .full_o     ( full         ),
        .empty_o    ( empty        ),
        .usage_o,
        .data_i     ( data_enc     ),
        .push_i     ( push         ),
        .data_o     ( data_enc_out ),
        .pop_i      ( pop          ),
        .fault_o    ( rel_fifo_fault )
    );

    hsiao_ecc_dec #(
        .DataWidth ( DataW ),
        .ProtWidth ( ProtW )
    ) i_ecc_dec (
        .in         ( data_enc_out ),
        .out        ( data_raw_out ),
        .syndrome_o ( ),
        .err_o      ( ecc_err      )
    );

    assign data_o       = T'(data_raw_out);
    // ecc_err is only meaningful while the head of the FIFO holds valid data
    assign fifo_fault_o = rel_fifo_fault | (valid_o & (|ecc_err));

endmodule
