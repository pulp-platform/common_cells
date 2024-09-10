// Copyright 2022 OpenHW Group
// Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

package addr_map_rule_pkg;

  typedef struct packed {
    logic [31:0] idx;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
  } addr_map_rule_t;

endpackage

package bus_type_pkg;

  typedef enum logic {
    NtoM,
    onetoM
  } bus_type_e;

  localparam bus_type_e BusType = onetoM;

endpackage
