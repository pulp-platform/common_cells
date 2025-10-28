// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Lorenzo Leone <lleone@iis.ee.ethz.ch>
//
// Contains common definition for the STREAM JOIN

package stream_join_pkg;

  // The stream join module can be used in different modes.
  // - ALL: the output valid is asserted only when all the selected inputs are valid.
  // - ANY: the output valid is asserted when any of the selected inputs is valid.
  typedef enum logic{
    ALL = 1'b0,
    ANY = 1'b1
  } stream_join_mode_e;

endpackage
