//-----------------------------------------------------------------------------
// Title : Stream Deposit
// -----------------------------------------------------------------------------
// File : stream_deposit.sv Author : Manuel Eggimann <meggimann@iis.ee.ethz.ch>
// Created : 17.05.2023
// -----------------------------------------------------------------------------
// Description :
//
// This module helps to deal with stream-sources that do not support
// backpressure i.e. cannot handle the case where the sink is not ready to
// accept a value. In constrast to a FIFO that queues the transactions, this IP
// just drops them. That is, the currently stalled in-flight transaction is just
// updated with the new data sent by the input. Therefore the input of this
// module is always ready but there is no guarantee that every transaction is
// sent to the output. The module will just keep the valid_o signal asserted
// until a transaction is acceted by the output side which at this point
// receives whatever data the input last deposited.
//
// The stream_deposit module is helpful to connect configuration registers with
// IPs that could cause back pressure. In this case we might not care how long
// it takes for the config value to be sent to the IP but if we change the
// config value we want the latest value to be used regardless wether the
// previous transaction was still in-fligth or not.
//
// IMPORTANT: The described behavior of this moduel obviously implies, that the data_o is
// not stable while valid_o is asserted. If you rely on this property, i.e. you
// are using the data before you accept the transaction, then you must not use
// this module!
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

module stream_deposit #(
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
    output T     data_o
);

  logic pending_d, pending_q;
  T data_d, data_q;

  assign data_d = valid_i ? data_i : data_q;
  // The pending flag is set if the input is valid and ready_i is not asserted.
  // It is cleared if it is currently set and the output side becomes ready.
  assign pending_d = (valid_i | pending_q) ? ~ready_i : pending_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      pending_q <= 1'b0;
      data_q    <= '0;
    end else begin
      pending_q <= pending_d;
      data_q    <= data_d;
    end
  end

  // If the input side is currently writing data, bypass the register.
  assign valid_o = valid_i | pending_q;
  assign data_o  = valid_i ? data_i : data_q;

endmodule
