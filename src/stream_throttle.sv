// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Thomas Benz <tbenz@ethz.ch>

`include "common_cells/registers.svh"

/// Throttles a ready valid handshaked bus. The maximum number of outstanding transfers have to
/// be set as a compile-time parameter, whereas the number of outstanding transfers can be set
/// during runtime. This module assumes either in-order processing of the requests or
/// indistinguishability of the request/responses.
module stream_throttle #(
    /// The maximum amount of allowable outstanding requests
    parameter int unsigned MaxNumPending = 1,
    /// The width of the credit counter (*DO NOT OVERWRITE*)
    parameter int unsigned CntWidth = cf_math_pkg::idx_width(MaxNumPending),
    /// The type of the credit counter (*DO NOT OVERWRITE*)
    parameter type credit_t = logic [CntWidth-1:0]
) (
    /// Clock
    input  logic clk_i,
    /// Asynchronous reset, active low
    input  logic rst_ni,

    /// Request valid in
    input  logic    req_valid_i,
    /// Request valid out
    output logic    req_valid_o,
    /// Request ready in
    input  logic    req_ready_i,
    /// Request ready out
    output logic    req_ready_o,

    /// Response valid in
    input  logic    rsp_valid_i,
    /// Response ready in
    input  logic    rsp_ready_i,

    /// Amount of credit (number of outstanding transfers)
    input  credit_t credit_i
);

    // we use a credit counter to keep track of how many transfers are pending at any point in
    // time. Valid is passed-through if there is credit.
    credit_t credit_d, credit_q;

    // we have credit available
    logic credit_available;

    // implement the counter. If credit is available let the valid pass, else block it. Increment
    // the counter once a request happens, decrement once a response arrives. Assumes in-order
    // responses.
    always_comb begin : proc_credit_counter

        // default: keep state
        credit_d = credit_q;

        // on valid outgoing request: count up
        if (req_ready_o & req_valid_o) begin
            credit_d = credit_d + 'd1;
        end

        // on valid response: count down
        if (rsp_valid_i & rsp_ready_i) begin
            credit_d = credit_d - 'd1;
        end
    end

    // credit is available
    assign credit_available = credit_q <= (credit_i - 'd1);

    // a request id passed on as valid if the input is valid and we have credit.
    assign req_valid_o = req_valid_i & credit_available;

    // a request id passed on as ready if the input is ready and we have credit.
    assign req_ready_o = req_ready_i & credit_available;

    // state
    `FF(credit_q, credit_d, '0, clk_i, rst_ni)

endmodule : stream_throttle
