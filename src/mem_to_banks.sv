// Copyright (c) 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Wolfgang Roenninger <wroennin@ethz.ch>

/// Split memory access over multiple parallel banks, where each bank has its own req/gnt
/// request and valid response direction.
module mem_to_banks #(
  /// Input address width.
  parameter int unsigned AddrWidth = 32'd0,
  /// Input data width, must be a power of two.
  parameter int unsigned DataWidth = 32'd0,
  /// Atop width.
  parameter int unsigned AtopWidth = 32'd0,
  /// Number of banks at output, must evenly divide `DataWidth`.
  parameter int unsigned NumBanks  = 32'd1,
  /// Remove transactions that have zero strobe
  parameter bit          HideStrb  = 1'b0,
  /// Number of outstanding transactions
  parameter int unsigned MaxTrans  = 32'd1,
  /// FIFO depth, must be >=1
  parameter int unsigned FifoDepth = 32'd1,
  /// Atop type.
  parameter  type atop_t     = logic [AtopWidth-1:0],
  /// Dependent parameter, do not override! Address type.
  localparam type addr_t     = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override! Input data type.
  localparam type inp_data_t = logic [DataWidth-1:0],
  /// Dependent parameter, do not override! Input write strobe type.
  localparam type inp_strb_t = logic [DataWidth/8-1:0],
  /// Dependent parameter, do not override! Output data type.
  localparam type oup_data_t = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override! Output write strobe type.
  localparam type oup_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  /// Clock input.
  input  logic                      clk_i,
  /// Asynchronous reset, active low.
  input  logic                      rst_ni,
  /// Memory request to split, request is valid.
  input  logic                      req_i,
  /// Memory request to split, request can be granted.
  output logic                      gnt_o,
  /// Memory request to split, request address, byte-wise.
  input  addr_t                     addr_i,
  /// Memory request to split, request write data.
  input  inp_data_t                 wdata_i,
  /// Memory request to split, request write strobe.
  input  inp_strb_t                 strb_i,
  /// Memory request to split, request Atomic signal from AXI4+ATOP.
  input  atop_t                     atop_i,
  /// Memory request to split, request write enable, active high.
  input  logic                      we_i,
  /// Memory request to split, response is valid. Required for read and write requests
  output logic                      rvalid_o,
  /// Memory request to split, response read data.
  output inp_data_t                 rdata_o,
  /// Memory bank request, request is valid.
  output logic      [NumBanks-1:0]  bank_req_o,
  /// Memory bank request, request can be granted.
  input  logic      [NumBanks-1:0]  bank_gnt_i,
  /// Memory bank request, request address, byte-wise. Will be different for each bank.
  output addr_t     [NumBanks-1:0]  bank_addr_o,
  /// Memory bank request, request write data.
  output oup_data_t [NumBanks-1:0]  bank_wdata_o,
  /// Memory bank request, request write strobe.
  output oup_strb_t [NumBanks-1:0]  bank_strb_o,
  /// Memory bank request, request Atomic signal from AXI4+ATOP.
  output atop_t     [NumBanks-1:0]  bank_atop_o,
  /// Memory bank request, request write enable, active high.
  output logic      [NumBanks-1:0]  bank_we_o,
  /// Memory bank request, response is valid. Required for read and write requests
  input  logic      [NumBanks-1:0]  bank_rvalid_i,
  /// Memory bank request, response read data.
  input  oup_data_t [NumBanks-1:0]  bank_rdata_i
);

  mem_to_banks_detailed #(
    .AddrWidth  ( AddrWidth  ),
    .DataWidth  ( DataWidth  ),
    .WUserWidth ( AtopWidth  ),
    .RUserWidth ( 1          ),
    .NumBanks   ( NumBanks   ),
    .HideStrb   ( HideStrb   ),
    .MaxTrans   ( MaxTrans   ),
    .FifoDepth  ( FifoDepth  ),
    .wuser_t    ( atop_t     )
  ) i_mem_to_banks_detailed (
    .clk_i,
    .rst_ni,
    .req_i,
    .gnt_o,
    .addr_i,
    .wdata_i,
    .strb_i,
    .wuser_i      ( atop_i ),
    .we_i,
    .rvalid_o,
    .rdata_o,
    .ruser_o      (),
    .bank_req_o,
    .bank_gnt_i,
    .bank_addr_o,
    .bank_wdata_o,
    .bank_strb_o,
    .bank_wuser_o ( bank_atop_o ),
    .bank_we_o,
    .bank_rvalid_i,
    .bank_rdata_i,
    .bank_ruser_i ('0)
  );

endmodule
