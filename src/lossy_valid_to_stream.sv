//-----------------------------------------------------------------------------
// Title : lossy_valid_to_stream
// -----------------------------------------------------------------------------
// File : lossy_valid_to_stream.sv Author : Manuel Eggimann
// <meggimann@iis.ee.ethz.ch> Created : 17.05.2023
// -----------------------------------------------------------------------------
// Description :
//
// This module helps to deal with sources that use a valid-only interace, that
// is they do not support backpressure i.e. cannot handle the case where the
// sink is not ready to accept a value. The module is implemented as FIFO with 2
// elements. In contrast to a regular FIFO that stops accepting new transactions
// once the FIFO is full, this IP overwrites the last element entered into the
// FIFO. This means the input is always ready to accept new transactions,
// however, intermediate transactions might be overwritten by the latest one. On
// the output side, the module behaves like a regular ready-valid source i.e.
// once valid is asserted, data_o remains stable until the sink consumes them
// (by asserting ready_i).

// IMPORTANT: As the name implies, this module might drop intermediate
// transactions if the input generates transactions faster than the sink can
// consume them. The input side can check if the last transaction was
// successfully comitted to the output by checking the
// busy_o signal. If it is de-asserted (low), there are no
// more outstanding transactions and the most recent value presented at the
// input side has been comitted to the output.
//
//
// The stream_deposit module is helpful to connect configuration registers with
// IPs that could cause back pressure. In this case we might not care how long
// it takes for the config value to be sent to the IP but if we change the
// config value we want the latest value to be used regardless wether the
// previous value has already been forwarded or not.
//
//
//-----------------------------------------------------------------------------
// Copyright (C) 2023 ETH Zurich, University of Bologna Copyright and related
// rights are licensed under the Solderpad Hardware License, Version 0.51 (the
// "License"); you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law or
// agreed to in writing, software, hardware and materials distributed under this
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, either express or implied. See the License for the specific
// language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
// -----------------------------------------------------------------------------

module lossy_valid_to_stream #(
    /// Default data width if the fifo is of type logic
    parameter int unsigned DATA_WIDTH = 32,
    parameter type T = logic [DATA_WIDTH-1:0]
) (
    input  logic clk_i,
    input  logic rst_ni,
    // Input Interface (the input is always ready so there is no ready_o signal)
    input  logic valid_i,
    input  T     data_i,
    // Output Interface
    output logic valid_o,
    input  logic ready_i,
    output T     data_o,
    // Status port
    output busy_o
);

  // Implement a FIFO with depth == 2 where the write logic can overwrite the
  // last element.

  logic read_ptr_d, read_ptr_q;
  logic write_ptr_d, write_ptr_q;
  logic [1:0] pending_tx_counter_d, pending_tx_counter_q;
  T[1:0] mem_d, mem_q;

  assign valid_o = pending_tx_counter_q != 0 || valid_i;

  always_comb begin : write_logic
    write_ptr_d = write_ptr_q;
    mem_d       = mem_q;
    if (valid_i) begin
      // If the FIFO is empty and the output is currently ready, fall through
      // the FIFO and don't update anything
      if (pending_tx_counter_q != 0 || !ready_i) begin
        // If the FIFO is full and the output is still stalling, update the
        // previous element instead of writing a new one and do not update the
        // write pointer
        if (pending_tx_counter_q == 2 && !ready_i) begin
          mem_d[write_ptr_q - 1'b1] = data_i;
        end else begin
          mem_d[write_ptr_q] = data_i;
          write_ptr_d = write_ptr_q + 1'b1;
        end
      end
    end
  end

  always_comb begin : read_logic
    read_ptr_d = read_ptr_q;
    data_o = mem_q[read_ptr_q];
    // Handle the fall-through case
    if (pending_tx_counter_q == 0 && valid_i) begin
      data_o = data_i;
    end else if (valid_o && ready_i) begin
      read_ptr_d = read_ptr_q + 1'b1;
    end
  end

  always_comb begin: count_transactions
    pending_tx_counter_d = pending_tx_counter_q;
    if (valid_i && valid_o && ready_i) begin
      pending_tx_counter_d = pending_tx_counter_q;
    end else if (valid_i && !(valid_o && ready_i)) begin
      // If the FIFO is already full, do not update the counter
      if (pending_tx_counter_q != 2) begin
        pending_tx_counter_d = pending_tx_counter_q + 1'b1;
      end
    end else if (!valid_i && (valid_o && ready_i)) begin
      pending_tx_counter_d = pending_tx_counter_q - 1'b1;
    end
  end

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      read_ptr_q           <= '0;
      write_ptr_q          <= '0;
      pending_tx_counter_q <= '0;
      mem_q                <= '0;
    end else begin
      read_ptr_q           <= read_ptr_d;
      write_ptr_q          <= write_ptr_d;
      pending_tx_counter_q <= pending_tx_counter_d;
      mem_q                <= mem_d;
    end
  end

  assign busy_o = pending_tx_counter_q != 0;

endmodule
