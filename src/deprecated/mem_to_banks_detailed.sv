// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_mem_to_banks_detailed instead.

module mem_to_banks_detailed #(
  parameter int unsigned AddrWidth  = 32'd0,
  parameter int unsigned DataWidth  = 32'd0,
  parameter int unsigned WUserWidth = 32'd0,
  parameter int unsigned RUserWidth = 32'd0,
  parameter int unsigned NumBanks   = 32'd1,
  parameter bit          HideStrb   = 1'b0,
  parameter int unsigned MaxTrans   = 32'd1,
  parameter int unsigned FifoDepth  = 32'd1,
  parameter  type wuser_t     = logic [WUserWidth-1:0],
  localparam type addr_t      = logic [AddrWidth-1:0],
  localparam type inp_data_t  = logic [DataWidth-1:0],
  localparam type inp_strb_t  = logic [DataWidth/8-1:0],
  localparam type inp_ruser_t = logic [NumBanks-1:0][RUserWidth-1:0],
  localparam type oup_data_t  = logic [DataWidth/NumBanks-1:0],
  localparam type oup_strb_t  = logic [DataWidth/NumBanks/8-1:0],
  localparam type oup_ruser_t = logic [RUserWidth-1:0]
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       req_i,
  output logic                       gnt_o,
  input  addr_t                      addr_i,
  input  inp_data_t                  wdata_i,
  input  inp_strb_t                  strb_i,
  input  wuser_t                     wuser_i,
  input  logic                       we_i,
  output logic                       rvalid_o,
  output inp_data_t                  rdata_o,
  output inp_ruser_t                 ruser_o,
  output logic       [NumBanks-1:0]  bank_req_o,
  input  logic       [NumBanks-1:0]  bank_gnt_i,
  output addr_t      [NumBanks-1:0]  bank_addr_o,
  output oup_data_t  [NumBanks-1:0]  bank_wdata_o,
  output oup_strb_t  [NumBanks-1:0]  bank_strb_o,
  output wuser_t     [NumBanks-1:0]  bank_wuser_o,
  output logic       [NumBanks-1:0]  bank_we_o,
  input  logic       [NumBanks-1:0]  bank_rvalid_i,
  input  oup_data_t  [NumBanks-1:0]  bank_rdata_i,
  input  oup_ruser_t [NumBanks-1:0]  bank_ruser_i
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_mem_to_banks_detailed' instead.");
  // synthesis translate_on
  cc_mem_to_banks_detailed #(
    .AddrWidth  ( AddrWidth  ),
    .DataWidth  ( DataWidth  ),
    .WUserWidth ( WUserWidth ),
    .RUserWidth ( RUserWidth ),
    .NumBanks   ( NumBanks   ),
    .HideStrb   ( HideStrb   ),
    .MaxTrans   ( MaxTrans   ),
    .FifoDepth  ( FifoDepth  ),
    .wuser_t    ( wuser_t    )
  ) i_cc_mem_to_banks_detailed (
    .clk_i         ( clk_i         ),
    .rst_ni        ( rst_ni        ),
    .clr_i         ( 1'b0          ),
    .req_i         ( req_i         ),
    .gnt_o         ( gnt_o         ),
    .addr_i        ( addr_i        ),
    .wdata_i       ( wdata_i       ),
    .strb_i        ( strb_i        ),
    .wuser_i       ( wuser_i       ),
    .we_i          ( we_i          ),
    .rvalid_o      ( rvalid_o      ),
    .rdata_o       ( rdata_o       ),
    .ruser_o       ( ruser_o       ),
    .bank_req_o    ( bank_req_o    ),
    .bank_gnt_i    ( bank_gnt_i    ),
    .bank_addr_o   ( bank_addr_o   ),
    .bank_wdata_o  ( bank_wdata_o  ),
    .bank_strb_o   ( bank_strb_o   ),
    .bank_wuser_o  ( bank_wuser_o  ),
    .bank_we_o     ( bank_we_o     ),
    .bank_rvalid_i ( bank_rvalid_i ),
    .bank_rdata_i  ( bank_rdata_i  ),
    .bank_ruser_i  ( bank_ruser_i  )
  );
endmodule
