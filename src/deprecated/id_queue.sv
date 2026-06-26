// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Deprecated: use cc_id_queue instead.

module id_queue #(
  parameter int          ID_WIDTH             = 0,
  parameter int          CAPACITY             = 0,
  parameter bit          FULL_BW              = 0,
  parameter bit          CUT_OUP_POP_INP_GNT  = 0,
  parameter int          NUM_CMP_PORTS        = 1,
  parameter type         data_t               = logic [31:0],
  localparam type        id_t                 = logic [ID_WIDTH-1:0]
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  id_t                           inp_id_i,
  input  data_t                         inp_data_i,
  input  logic                          inp_req_i,
  output logic                          inp_gnt_o,
  input  data_t [NUM_CMP_PORTS-1:0]    exists_data_i,
  input  data_t [NUM_CMP_PORTS-1:0]    exists_mask_i,
  input  logic  [NUM_CMP_PORTS-1:0]    exists_req_i,
  output logic  [NUM_CMP_PORTS-1:0]    exists_o,
  output logic  [NUM_CMP_PORTS-1:0]    exists_gnt_o,
  input  id_t                           oup_id_i,
  input  logic                          oup_pop_i,
  input  logic                          oup_req_i,
  output data_t                         oup_data_o,
  output logic                          oup_data_valid_o,
  output logic                          oup_gnt_o,
  output logic                          full_o,
  output logic                          empty_o
);
  // synthesis translate_off
  initial $warning("Module '%m' is deprecated. Use 'cc_id_queue' instead.");
  // synthesis translate_on
  cc_id_queue #(
    .ID_WIDTH            ( ID_WIDTH            ),
    .CAPACITY            ( CAPACITY            ),
    .FULL_BW             ( FULL_BW             ),
    .CUT_OUP_POP_INP_GNT ( CUT_OUP_POP_INP_GNT ),
    .NUM_CMP_PORTS       ( NUM_CMP_PORTS       ),
    .data_t              ( data_t              )
  ) i_cc_id_queue (
    .clk_i           ( clk_i           ),
    .rst_ni          ( rst_ni          ),
    .inp_id_i        ( inp_id_i        ),
    .inp_data_i      ( inp_data_i      ),
    .inp_req_i       ( inp_req_i       ),
    .inp_gnt_o       ( inp_gnt_o       ),
    .exists_data_i   ( exists_data_i   ),
    .exists_mask_i   ( exists_mask_i   ),
    .exists_req_i    ( exists_req_i    ),
    .exists_o        ( exists_o        ),
    .exists_gnt_o    ( exists_gnt_o    ),
    .oup_id_i        ( oup_id_i        ),
    .oup_pop_i       ( oup_pop_i       ),
    .oup_req_i       ( oup_req_i       ),
    .oup_data_o      ( oup_data_o      ),
    .oup_data_valid_o( oup_data_valid_o),
    .oup_gnt_o       ( oup_gnt_o       ),
    .full_o          ( full_o          ),
    .empty_o         ( empty_o         )
  );
endmodule
