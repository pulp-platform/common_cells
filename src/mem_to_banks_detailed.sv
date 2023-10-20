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
module mem_to_banks_detailed #(
  /// Input address width.
  parameter int unsigned AddrWidth = 32'd0,
  /// Input data width, must be a power of two.
  parameter int unsigned DataWidth = 32'd0,
  /// Request sideband width.
  parameter int unsigned WUserWidth = 32'd0,
  /// Response sideband width.
  parameter int unsigned RUserWidth = 32'd0,
  /// Number of banks at output, must evenly divide `DataWidth`.
  parameter int unsigned NumBanks  = 32'd1,
  /// Remove transactions that have zero strobe
  parameter bit          HideStrb  = 1'b0,
  /// Number of outstanding transactions
  parameter int unsigned MaxTrans  = 32'd1,
  /// FIFO depth, must be >=1
  parameter int unsigned FifoDepth = 32'd1,
  /// Request sideband type.
  parameter  type wuser_t     = logic [WUserWidth-1:0],
  /// Dependent parameter, do not override! Address type.
  localparam type addr_t      = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override! Input data type.
  localparam type inp_data_t  = logic [DataWidth-1:0],
  /// Dependent parameter, do not override! Input write strobe type.
  localparam type inp_strb_t  = logic [DataWidth/8-1:0],
  /// Dependent parameter, do not override! Input response sideband type.
  localparam type inp_ruser_t = logic [NumBanks-1:0][RUserWidth-1:0],
  /// Dependent parameter, do not override! Output data type.
  localparam type oup_data_t  = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override! Output write strobe type.
  localparam type oup_strb_t  = logic [DataWidth/NumBanks/8-1:0],
  /// Dependent parameter, do not override! Output response sideband type.
  localparam type oup_ruser_t = logic [RUserWidth-1:0]
) (
  /// Clock input.
  input  logic                       clk_i,
  /// Asynchronous reset, active low.
  input  logic                       rst_ni,
  /// Memory request to split, request is valid.
  input  logic                       req_i,
  /// Memory request to split, request can be granted.
  output logic                       gnt_o,
  /// Memory request to split, request address, byte-wise.
  input  addr_t                      addr_i,
  /// Memory request to split, request write data.
  input  inp_data_t                  wdata_i,
  /// Memory request to split, request write strobe.
  input  inp_strb_t                  strb_i,
  /// Memory request to split, request sideband.
  input  wuser_t                     wuser_i,
  /// Memory request to split, request write enable, active high.
  input  logic                       we_i,
  /// Memory request to split, response is valid. Required for read and write requests
  output logic                       rvalid_o,
  /// Memory request to split, response read data.
  output inp_data_t                  rdata_o,
  /// Memory request to split, response sideband.
  output inp_ruser_t                 ruser_o,
  /// Memory bank request, request is valid.
  output logic       [NumBanks-1:0]  bank_req_o,
  /// Memory bank request, request can be granted.
  input  logic       [NumBanks-1:0]  bank_gnt_i,
  /// Memory bank request, request address, byte-wise. Will be different for each bank.
  output addr_t      [NumBanks-1:0]  bank_addr_o,
  /// Memory bank request, request write data.
  output oup_data_t  [NumBanks-1:0]  bank_wdata_o,
  /// Memory bank request, request write strobe.
  output oup_strb_t  [NumBanks-1:0]  bank_strb_o,
  /// Memory bank request, request sideband.
  output wuser_t     [NumBanks-1:0]  bank_wuser_o,
  /// Memory bank request, request write enable, active high.
  output logic       [NumBanks-1:0]  bank_we_o,
  /// Memory bank request, response is valid. Required for read and write requests
  input  logic       [NumBanks-1:0]  bank_rvalid_i,
  /// Memory bank request, response read data.
  input  oup_data_t  [NumBanks-1:0]  bank_rdata_i,
  /// Memory bank request, response sideband.
  input  oup_ruser_t [NumBanks-1:0]  bank_ruser_i
);

  localparam int unsigned DataBytes    = $bits(inp_strb_t);
  localparam int unsigned BitsPerBank  = $bits(oup_data_t);
  localparam int unsigned BytesPerBank = $bits(oup_strb_t);

  typedef struct packed {
    addr_t     addr;
    oup_data_t wdata;
    oup_strb_t strb;
    wuser_t    wuser;
    logic      we;
  } req_t;

  logic                 req_valid;
  logic [NumBanks-1:0]              req_ready,
                        resp_valid, resp_ready;
  req_t [NumBanks-1:0]  bank_req,
                        bank_oup;
  logic [NumBanks-1:0]  bank_req_internal, bank_gnt_internal, zero_strobe, dead_response;
  logic                 dead_write_fifo_full;

  function automatic addr_t align_addr(input addr_t addr);
    return (addr >> $clog2(DataBytes)) << $clog2(DataBytes);
  endfunction

  // Handle requests.
  assign req_valid = req_i & gnt_o;
  for (genvar i = 0; unsigned'(i) < NumBanks; i++) begin : gen_reqs
    assign bank_req[i].addr  = align_addr(addr_i) + i * BytesPerBank;
    assign bank_req[i].wdata = wdata_i[i*BitsPerBank+:BitsPerBank];
    assign bank_req[i].strb  = strb_i[i*BytesPerBank+:BytesPerBank];
    assign bank_req[i].wuser = wuser_i;
    assign bank_req[i].we    = we_i;
    stream_fifo #(
      .FALL_THROUGH ( 1'b1         ),
      .DATA_WIDTH   ( $bits(req_t) ),
      .DEPTH        ( FifoDepth    ),
      .T            ( req_t        )
    ) i_ft_reg (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0          ),
      .testmode_i ( 1'b0          ),
      .usage_o    (),
      .data_i     ( bank_req[i]   ),
      .valid_i    ( req_valid     ),
      .ready_o    ( req_ready[i]  ),
      .data_o     ( bank_oup[i]   ),
      .valid_o    ( bank_req_internal[i] ),
      .ready_i    ( bank_gnt_internal[i] )
    );
    assign bank_addr_o[i]  = bank_oup[i].addr;
    assign bank_wdata_o[i] = bank_oup[i].wdata;
    assign bank_strb_o[i]  = bank_oup[i].strb;
    assign bank_wuser_o[i] = bank_oup[i].wuser;
    assign bank_we_o[i]    = bank_oup[i].we;

    assign zero_strobe[i] = (bank_oup[i].strb == '0);

    if (HideStrb) begin : gen_hide_strb
      assign bank_req_o[i] = (bank_oup[i].we && zero_strobe[i]) ? 1'b0 : bank_req_internal[i];
      assign bank_gnt_internal[i] = (bank_oup[i].we && zero_strobe[i]) ? 1'b1 : bank_gnt_i[i];
    end else begin : gen_legacy_strb
      assign bank_req_o[i] = bank_req_internal[i];
      assign bank_gnt_internal[i] = bank_gnt_i[i];
    end
  end

  // Grant output if all our requests have been granted.
  assign gnt_o = (&req_ready) & (&resp_ready) & !dead_write_fifo_full;

  if (HideStrb) begin : gen_dead_write_fifo
    fifo_v3 #(
      .FALL_THROUGH ( 1'b0     ),
      .DEPTH        ( MaxTrans+1 ),
      .DATA_WIDTH   ( NumBanks )
    ) i_dead_write_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0                    ),
      .testmode_i ( 1'b0                    ),
      .full_o     ( dead_write_fifo_full    ),
      .empty_o    (),
      .usage_o    (),
      .data_i     ( bank_we_o & zero_strobe ),
      .push_i     ( req_i & gnt_o           ),
      .data_o     ( dead_response           ),
      .pop_i      ( rvalid_o                )
    );
  end else begin : gen_no_dead_write_fifo
    assign dead_response = '0;
    assign dead_write_fifo_full = 1'b0;
  end

  // Handle responses.
  for (genvar i = 0; unsigned'(i) < NumBanks; i++) begin : gen_resp_regs
    stream_fifo #(
      .FALL_THROUGH ( 1'b1              ),
      .DATA_WIDTH   ( $bits(oup_data_t) + $bits(oup_ruser_t) ),
      .DEPTH        ( FifoDepth         )
    ) i_ft_reg (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0                                              ),
      .testmode_i ( 1'b0                                              ),
      .usage_o    (),
      .data_i     ( {bank_rdata_i[i], bank_ruser_i[i]}                ),
      .valid_i    ( bank_rvalid_i[i]                                  ),
      .ready_o    ( resp_ready[i]                                     ),
      .data_o     ( {rdata_o[i*BitsPerBank+:BitsPerBank], ruser_o[i]} ),
      .valid_o    ( resp_valid[i]                                     ),
      .ready_i    ( rvalid_o & !dead_response[i]                      )
    );
  end
  assign rvalid_o = &(resp_valid | dead_response);

  // Assertions
  // pragma translate_off
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ifndef SYNTHESIS
    initial begin
      assume (DataWidth != 0 && (DataWidth & (DataWidth - 1)) == 0)
        else $fatal(1, "Data width must be a power of two!");
      assume (DataWidth % NumBanks == 0)
        else $fatal(1, "Data width must be evenly divisible over banks!");
      assume ((DataWidth / NumBanks) % 8 == 0)
        else $fatal(1, "Data width of each bank must be divisible into 8-bit bytes!");
    end
  `endif
  `endif
  // pragma translate_on
endmodule
