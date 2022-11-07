// Copyright 2022 EPFL
// Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

// Author: Davide Schiavone, EPFL, OpenHW Group
// Date: 07.11.2022
// Description: Dummy circuit to assign a signal, prevent signal being removed after non-ungroupped synthesis compilation

module read (
    input  logic d_i,
    output logic d_o
);

  assign d_o = d_i;

endmodule
