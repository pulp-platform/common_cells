// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Wolfgang Roenninger <wroennin@ethz.ch>, ETH Zurich
//
// ## Description:
//    Test to address the multibanked powergated SRAM and checlk correct address handling.

module mem_multibank_pwrgate_tb #(
    parameter int unsigned NumPorts      = 32'd2,
    parameter int unsigned Latency       = 32'd1,
    parameter int unsigned NumWords      = 32'd1024,
    parameter int unsigned DataWidth     = 32'd64,
    parameter int unsigned ByteWidth     = 32'd8,
    parameter int unsigned NoReq         = 32'd200000,
    parameter int unsigned NumLogicBanks = 32'd1,
    parameter string       SimInit       = "zeros",
    parameter time         CyclTime      = 10ns,
    parameter time         ApplTime      = 2ns,
    parameter time         TestTime      = 8ns
);

   //-----------------------------------
   // Clock generator
   //-----------------------------------
   logic clk, rst_n;
   clk_rst_gen #(
       .ClkPeriod   (CyclTime),
       .RstClkCycles(5)
   ) i_clk_gen (
       .clk_o (clk),
       .rst_no(rst_n)
   );

   logic [NumPorts-1:0] done;

   localparam int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1;
   localparam int unsigned BeWidth = (DataWidth + ByteWidth - 32'd1) / ByteWidth;

   typedef logic [AddrWidth-1:0] addr_t;
   typedef logic [DataWidth-1:0] data_t;
   typedef logic [BeWidth-1:0] be_t;

   // signal declarations for each sram
   logic [NumPorts-1:0] req, we;
   addr_t [NumPorts-1:0] addr;
   data_t [NumPorts-1:0] wdata, rdata;
   be_t             [NumPorts-1:0] be;

   // golden model
   data_t                          memory      [NumWords-1:0];
   longint unsigned                failed_test;

   // This process drives the requests on the port with random data.
   for (genvar i = 0; i < NumPorts; i++) begin : gen_stimuli
      initial begin : proc_drive_port
         automatic logic  stim_write;
         automatic addr_t stim_addr;
         automatic data_t stim_data;
         automatic be_t   stim_be;

         done[i]  <= 1'b0;
         req[i]   <= 1'b0;
         we[i]    <= 1'b0;
         addr[i]  <= addr_t'(0);
         wdata[i] <= data_t'(0);
         be[i]    <= be_t'(0);

         @(posedge rst_n);
         repeat (10) @(posedge clk);

         for (int unsigned j = 0; j < NoReq; j++) begin
            stim_write = bit'($urandom());
            for (int unsigned k = 0; k < AddrWidth; k++) begin
               stim_addr[k] = bit'($urandom());
            end
            // this statement makes sure that only valid addresses are in a request
            while (stim_addr >= NumWords) begin
               for (int unsigned k = 0; k < AddrWidth; k++) begin
                  stim_addr[k] = bit'($urandom());
               end
            end
            for (int unsigned k = 0; k < DataWidth; k++) begin
               stim_data[k] = bit'($urandom());
            end
            for (int unsigned k = 0; k < BeWidth; k++) begin
               stim_be[k] = bit'($urandom());
            end

            req[i]   <= #ApplTime 1'b1;
            we[i]    <= #ApplTime stim_write;
            addr[i]  <= #ApplTime stim_addr;
            wdata[i] <= #ApplTime stim_data;
            be[i]    <= #ApplTime stim_be;
            @(posedge clk);
            req[i]   <= #ApplTime 1'b0;
            we[i]    <= #ApplTime 1'b0;
            addr[i]  <= #ApplTime addr_t'(0);
            wdata[i] <= #ApplTime data_t'(0);
            be[i]    <= #ApplTime be_t'(0);

            repeat ($urandom_range(0, 5)) @(posedge clk);
         end
         done[i] <= 1'b1;
      end
   end

   // This process controls the golden model
   // - The memory array is initialized according to the parameter
   // - Data is written exactly at the clock edge, if there is a write request on a port.
   // - At `TestTime` a process is launched on read requests which lives for `Latency` cycles.
   //   This process asserts the expected read output at `TestTime` in the respective cycle.
   initial begin : proc_golden_model
      failed_test = 0;
      for (int unsigned i = 0; i < NumWords; i++) begin
         for (int unsigned j = 0; j < DataWidth; j++) begin
            case (SimInit)
               "zeros": memory[i][j] = 1'b0;
               "ones":  memory[i][j] = 1'b1;
               default: memory[i][j] = 1'bx;
            endcase
         end
      end

      @(posedge rst_n);

      forever begin
         @(posedge clk);
         // writes get latched at clock in golden model array
         for (int unsigned i = 0; i < NumPorts; i++) begin
            if (req[i] && we[i]) begin
               for (int unsigned j = 0; j < DataWidth; j++) begin
                  if (be[i][j/ByteWidth]) begin
                     memory[addr[i]][j] = wdata[i][j];
                  end
               end
            end
         end

         // read test process is launched at `TestTime`
         #TestTime;
         fork
            for (int unsigned i = 0; i < NumPorts; i++) begin
               check_read(i, addr[i]);
            end
         join_none
      end
   end

   // Read test process. This task lives for a number of cycles determined by `Latency`.
   task automatic check_read(input int unsigned port, input addr_t read_addr);
      // only continue if there is a read request at this port
      if (req[port] && !we[port]) begin
         data_t exp_data = memory[read_addr];

         if (Latency > 0) begin
            repeat (Latency) @(posedge clk);
            #TestTime;
         end

         for (int unsigned i = 0; i < DataWidth; i++) begin
            if (!$isunknown(exp_data[i])) begin
               assert (exp_data[i] === rdata[port][i])
               else begin
                  $warning("Port: %0d unexpected bit[%0h], Addr: %0h expected: %0h, measured: %0h",
                           port, i, read_addr, exp_data[i], rdata[port][i]);
                  failed_test++;
               end
            end
         end
      end
   endtask : check_read

   // Stop the simulation at the end.
   initial begin : proc_stop
      @(posedge rst_n);
      wait (&done);
      repeat (10) @(posedge clk);
      $info("Simulation done, errors: %0d", failed_test);
      $stop();
   end

   mem_multibank_pwrgate #(
       .NumWords     (NumWords),       // Number of Words in data array
       .DataWidth    (DataWidth),      // Data signal width
       .ByteWidth    (ByteWidth),      // Width of a data byte
       .NumPorts     (NumPorts),       // Number of read and write ports
       .Latency      (Latency),        // Latency when the read data is available
       .NumLogicBanks(NumLogicBanks),  // Number of Logic Banks for power gating/retention
       .SimInit      (SimInit),        // Simulation initialization
       .PrintSimCfg  (1'b1)            // Print configuration
   ) i_tc_sram_dut (
       .clk_i      (clk),    // Clock
       .rst_ni     (rst_n),  // Asynchronous reset active low
       .req_i      (req),    // request
       .we_i       (we),     // write enable
       .addr_i     (addr),   // request address
       .wdata_i    (wdata),  // write data
       .be_i       (be),     // write byte enable
       .deepsleep_i('0),     // Tied to zero to suppress Warnings
       .powergate_i('0),     // Tied to zero to suppress Warnings
       .rdata_o    (rdata)   // read data
   );

endmodule
