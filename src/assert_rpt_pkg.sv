// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef UVM
package assert_rpt_pkg;

  import uvm_pkg::*;

  `include "uvm_macros.svh"

  function automatic void assert_rpt(string msg);
    `uvm_error("ASSERT FAILED", msg)
  endfunction

endpackage
`endif
