// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package cc_pkg;

  //--------------------------------------------------------------------------
  // Mathematical functions
  //--------------------------------------------------------------------------
  // These functions are implemented as Verilog constant functions.
  // Introduced in Verilog 2001 (IEEE Std 1364-2001), a constant function (§ 10.3.5) is a
  // function whose value can be evaluated at compile time or during elaboration.  A constant function
  // must be called with arguments that are constants.

  /// Ceiled Division of Two Natural Numbers
  ///
  /// Returns the quotient of two natural numbers, rounded towards plus infinity.
  function automatic integer ceil_div (input longint dividend, input longint divisor);
    automatic longint remainder;

    `ifndef SYNTHESIS
    `ifndef COMMON_CELLS_ASSERTS_OFF
    if (dividend < 0) begin
      $fatal(1, "Dividend %0d is not a natural number!", dividend);
    end

    if (divisor < 0) begin
      $fatal(1, "Divisor %0d is not a natural number!", divisor);
    end

    if (divisor == 0) begin
      $fatal(1, "Division by zero!");
    end
    `endif
    `endif

    remainder = dividend;
    for (ceil_div = 0; remainder > 0; ceil_div++) begin
      remainder = remainder - divisor;
    end
  endfunction

  /// Index width required to be able to represent up to `num_idx` indices as a binary
  /// encoded signal.
  /// Ensures that the minimum width if an index signal is `1`, regardless of parametrization.
  function automatic integer unsigned idx_width (input integer unsigned num_idx);
    return (num_idx > 32'd1) ? unsigned'($clog2(num_idx)) : 32'd1;
  endfunction

  /// Checks if a value is a power of 2 (and is not 0)
  /// Returns 1 if the input value is a power of 2, else 0
  function automatic bit is_power_of_2 (input integer unsigned value);
    return (value != 0) && (value & (value - 1)) == 0;
  endfunction

  // Return either the argument minus 1 or 0 if 0; useful for IO vector width declaration.
  function automatic integer unsigned iomsb (input integer unsigned width);
    return (width != 32'd0) ? unsigned'(width-1) : 32'd0;
  endfunction

  /// Returns the maximum between two integers
  function automatic int max(int a, int b);
    if (a >= b) begin
      return a;
    end
    return b;
  endfunction

  /// Returns the minimum between two integers
  function automatic int min(int a, int b);
    if (a >= b) begin
      return b;
    end
    return a;
  endfunction

  //--------------------------------------------------------------------------
  // Bloom filter
  //--------------------------------------------------------------------------

  typedef struct packed {
    int unsigned PermuteSeed;
    int unsigned XorSeed;
  } cb_seed_t;

  // example seeding struct
  localparam cb_seed_t [2:0] cb_eg_seeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };

  //--------------------------------------------------------------------------
  // ECC
  //--------------------------------------------------------------------------

  // Calculate required ECC parity width:
  function automatic int unsigned ecc_get_parity_width (input int unsigned data_width);
    // data_width + cw_width + 1 <= 2**cw_width
    int unsigned cw_width = 2;
    while (unsigned'(2**cw_width) < cw_width + data_width + 1) cw_width++;
    return cw_width;
  endfunction

  // Calculate required ECC codeword width:
  function automatic int unsigned ecc_get_cw_width (input int unsigned data_width);
    // data width + parity width + one additional parity bit (for double error detection)
    return data_width + ecc_get_parity_width(data_width);
  endfunction

  //--------------------------------------------------------------------------
  // LZC
  //--------------------------------------------------------------------------

  typedef enum logic {
    LZC_TRAILING_ZERO_CNT = 1'b0,
    LZC_LEADING_ZERO_CNT = 1'b1
  } lzc_mode_e;

  //--------------------------------------------------------------------------
  // CDC reset controller
  //--------------------------------------------------------------------------

  typedef enum logic[1:0] {
    CDC_CLEAR_PHASE_IDLE,
    CDC_CLEAR_PHASE_ISOLATE,
    CDC_CLEAR_PHASE_CLEAR,
    CDC_CLEAR_PHASE_POST_CLEAR
  } cdc_clear_seq_phase_e;

endpackage
