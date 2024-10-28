// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Lorenzo Leone <lleone@iis.ee.ethz.ch>

// ## Description:
//   A wrapper for `tc_sram_impl` that instantiates logic banks with retention mode
//   or power-off capability.
//   This module can be used for power-aware simulations, with control signals driven
//   directly by UPF signals.
//
// ## Goal:
//   In a memory with multiple banks that support power gating and retention,
//   each bank’s addressing must ensure that interleaving remains intact. During retention
//   or power-off states, only contiguous addresses should be switched.
//   The memory should always appear as a set of contiguous addresses, with no gaps in the
//   address mapping.
//   This module is responsible for managing the correct memory addressing
//
module mem_multibank_pwrgate #(
    parameter int unsigned NumWords = 32'd1024,                                   // Number of Words in data array
    parameter int unsigned DataWidth = 32'd128,                                   // Data signal width
    parameter int unsigned ByteWidth = 32'd8,                                     // Width of a data byte
    parameter int unsigned NumPorts = 32'd2,                                      // Number of read and write ports
    parameter int unsigned Latency = 32'd1,                                       // Latency when the read data is available
    parameter int unsigned NumLogicBanks = 32'd1,                                 // Logic bank for Power Management
    parameter              SimInit = "none",                                      // Simulation initialization
    parameter bit          PrintSimCfg = 1'b0,                                    // Print configuration
    parameter              ImplKey = "none",                                      // Reference to specific implementation
    // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
    parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
    parameter int unsigned BeWidth = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
    parameter type         addr_t = logic [AddrWidth-1:0],
    parameter type         data_t = logic [DataWidth-1:0],
    parameter type         be_t = logic [BeWidth-1:0]
) (
    input  logic                      clk_i,        // Clock
    input  logic                      rst_ni,       // Asynchronous reset active low
    // input ports
    input  logic  [     NumPorts-1:0] req_i,        // request
    input  logic  [     NumPorts-1:0] we_i,         // write enable
    input  addr_t [     NumPorts-1:0] addr_i,       // request address
    input  data_t [     NumPorts-1:0] wdata_i,      // write data
    input  be_t   [     NumPorts-1:0] be_i,         // write byte enable
    input  logic  [NumLogicBanks-1:0] deepsleep_i,  // deep sleep enable
    input  logic  [NumLogicBanks-1:0] powergate_i,  // power gate enable
    // output ports
    output data_t [     NumPorts-1:0] rdata_o       // read data
);

   // Implementation type for Power Gating and Deppesleep ports
   typedef struct packed {
      logic deepsleep;
      logic powergate;
   } impl_in_t;


   if (NumLogicBanks == 32'd0) begin : gen_no_logic_bank
      $fatal("Error: %d logic banks are not supported", NumLogicBanks);
   end else if (NumLogicBanks == 32'd1) begin : gen_simple_sram
      tc_sram_impl #(
          .NumWords   (NumWords),
          .DataWidth  (DataWidth),
          .ByteWidth  (ByteWidth),
          .NumPorts   (NumPorts),
          .Latency    (Latency),
          .SimInit    (SimInit),
          .PrintSimCfg(PrintSimCfg),
          .ImplKey    (ImplKey),
          .impl_in_t  (impl_in_t),
          .impl_out_t (impl_in_t)
      ) i_tc_sram_impl (
          .clk_i,
          .rst_ni,
          .impl_i({deepsleep_i, powergate_i}),
          .impl_o(),
          .req_i,
          .we_i,
          .addr_i,
          .wdata_i,
          .be_i,
          .rdata_o
      );

   end else begin : gen_logic_bank  // block: gen_simple_sram
      localparam int unsigned LogicBankSize = NumWords / NumLogicBanks;
      localparam int unsigned BankSelWidth = (NumLogicBanks > 32'd1) ? $clog2(
          NumLogicBanks
      ) : 32'd1;

      if (LogicBankSize != 2 ** (AddrWidth - BankSelWidth))
         $fatal("Logic Bank size is not a power of two: UNSUPPORTED ");

      // Signals from/to logic banks
      logic  [NumLogicBanks-1:0][    NumPorts-1:0]                             req_cut;
      logic  [NumLogicBanks-1:0][    NumPorts-1:0]                             we_cut;
      logic  [NumLogicBanks-1:0][    NumPorts-1:0][AddrWidth-BankSelWidth-1:0] addr_cut;
      data_t [NumLogicBanks-1:0][    NumPorts-1:0]                             wdata_cut;
      be_t   [NumLogicBanks-1:0][    NumPorts-1:0]                             be_cut;
      data_t [NumLogicBanks-1:0][    NumPorts-1:0]                             rdata_cut;

      // Signals to select the right bank
      logic  [     NumPorts-1:0][BankSelWidth-1:0]                             bank_sel;
      logic [NumPorts-1:0][Latency-1:0][BankSelWidth-1:0] out_mux_sel_d, out_mux_sel_q;

      // Identify bank looking at the BankSelWidth-th MSBs of the Address
      for (genvar PortIdx = 0; PortIdx < NumPorts; PortIdx++) begin : gen_bank_sel
         assign bank_sel[PortIdx] = addr_i[PortIdx][AddrWidth-1-:BankSelWidth];
      end

      // Read Data Mux Logic:
      //
      // If the memory has Latency != 0, the read data will arive after a certain delay.
      // During this time, the bank_select signal must be stored in order to
      // correctly select the output bank after the expected latency.
      if (Latency == 32'd0) begin : gen_no_latency
         for (genvar PortIdx = 0; PortIdx < NumPorts; PortIdx++) begin : gen_read_mux_signals
            assign rdata_o[PortIdx] = rdata_cut[bank_sel[PortIdx]][PortIdx];
         end
      end else begin : gen_read_latency
         always_comb begin
            for (int PortIdx = 0; PortIdx < NumPorts; PortIdx++) begin : gen_read_mux_signals
               rdata_o[PortIdx] = rdata_cut[out_mux_sel_q[PortIdx][0]][PortIdx];
               for (int shift_idx = 0; shift_idx < (Latency - 1); shift_idx++) begin : gen_shift
                  out_mux_sel_d[PortIdx][shift_idx] = out_mux_sel_q[PortIdx][shift_idx+1];
               end
               out_mux_sel_d[PortIdx][Latency-1] = bank_sel[PortIdx];
            end
         end

         always_ff @(posedge clk_i or negedge rst_ni) begin
            for (int PortIdx = 0; PortIdx < NumPorts; PortIdx++) begin
               if (!rst_ni) begin
                  out_mux_sel_q[PortIdx] = '0;
               end else begin
                  for (int shift_idx = 0; shift_idx < Latency; shift_idx++) begin
                     out_mux_sel_q[PortIdx][shift_idx] = out_mux_sel_d[PortIdx][shift_idx];
                  end
               end
            end
         end
      end : gen_read_latency

      // Write data Mux Logic
      //
      for (genvar BankIdx = 0; BankIdx < NumLogicBanks; BankIdx++) begin : gen_logic_bank
         for (genvar PortIdx = 0; PortIdx < NumPorts; PortIdx++) begin
            // DEMUX the input signals to the correct logic bank
            // Assign req channel to the correct logic bank
            assign req_cut[BankIdx][PortIdx] = req_i[PortIdx] && (bank_sel[PortIdx] == BankIdx);
            // Assign lowest part of the address to the correct logic bank
            assign addr_cut[BankIdx][PortIdx]  = req_cut[BankIdx][PortIdx] ? addr_i[PortIdx][AddrWidth-BankSelWidth-1:0] : '0;
            // Assign data to the correct logic bank
            assign wdata_cut[BankIdx][PortIdx] = req_cut[BankIdx][PortIdx] ? wdata_i[PortIdx] : '0;
            assign we_cut[BankIdx][PortIdx] = req_cut[BankIdx][PortIdx] ? we_i[PortIdx] : '0;
            assign be_cut[BankIdx][PortIdx] = req_cut[BankIdx][PortIdx] ? be_i[PortIdx] : '0;
         end

         tc_sram_impl #(
             .NumWords   (LogicBankSize),
             .DataWidth  (DataWidth),
             .ByteWidth  (ByteWidth),
             .NumPorts   (NumPorts),
             .Latency    (Latency),
             .SimInit    (SimInit),
             .PrintSimCfg(PrintSimCfg),
             .ImplKey    (ImplKey),
             .impl_in_t  (impl_in_t),
             .impl_out_t (impl_in_t)
         ) i_tc_sram_impl (
             .clk_i,
             .rst_ni,
             .impl_i ({deepsleep_i[BankIdx], powergate_i[BankIdx]}),
             .impl_o (),
             .req_i  (req_cut[BankIdx]),
             .we_i   (we_cut[BankIdx]),
             .addr_i (addr_cut[BankIdx]),
             .wdata_i(wdata_cut[BankIdx]),
             .be_i   (be_cut[BankIdx]),
             .rdata_o(rdata_cut[BankIdx])
         );
      end
   end

   // Trigger warnings when power signals (deepsleep_i and powergate_i) are not connected.
   // Usually those signals must be linked through the UPF.
`ifndef VERILATOR
`ifndef TARGET_SYNTHESIS
   initial begin
      assert (!$isunknown(deepsleep_i))
      else $warning("deepsleep_i has some unconnected signals");
      assert (!$isunknown(powergate_i))
      else $warning("powergate_i has some unconnected signals");
   end
`endif
`endif

endmodule  //endmodule: mem_multibank_pwrgate
