# Common Cells Repository

Maintainer: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

This repository contains commonly used cells and headers for use in various projects.

## Cell Contents

This repository currently contains the following cells, ordered by categories.
Please note that cells with status *deprecated* are not to be used for new designs and only serve to provide compatibility with old code.

### Clocks and Resets

|           Name          |                     Description                     |    Status    |
|-------------------------|-----------------------------------------------------|--------------|
| `clk_div`               | Clock divider with integer divisor                  | active       |
| `clock_divider`         | Clock divider with configuration registers          | *deprecated* |
| `clock_divider_counter` | Clock divider using a counter                       | *deprecated* |
| `rstgen`                | Reset synchronizer                                  | active       |
| `rstgen_bypass`         | Reset synchronizer with dedicated test reset bypass | active       |

### Clock Domains and Asynchronous Crossings

|         Name         |                                   Description                                    |    Status    |
|----------------------|----------------------------------------------------------------------------------|--------------|
| `cdc_2phase`         | Clock domain crossing using two-phase handshake, with ready/valid interface      | active       |
| `cdc_fifo_2phase`    | Clock domain crossing FIFO using two-phase handshake, with ready/valid interface | active       |
| `cdc_fifo_gray`      | Clock domain crossing FIFO using a gray-counter, with ready/valid interface      | active       |
| `edge_detect`        | Rising/falling edge detector                                                     | active       |
| `edge_propagator`    | **ANTONIO ADD DESCRIPTION**                                                      | active       |
| `edge_propagator_rx` | **ANTONIO ADD DESCRIPTION**                                                      | active       |
| `edge_propagator_tx` | **ANTONIO ADD DESCRIPTION**                                                      | active       |
| `pulp_sync`          | Serial line synchronizer                                                         | *deprecated* |
| `pulp_sync_wedge`    | Serial line synchronizer with edge detector                                      | *deprecated* |
| `serial_deglitch`    | Serial line deglitcher                                                           | active       |
| `sync`               | Serial line synchronizer                                                         | active       |
| `sync_wedge`         | Serial line synchronizer with edge detector                                      | active       |

### Counters and Shift Registers

|         Name        |                   Description                   |    Status    |
|---------------------|-------------------------------------------------|--------------|
| `counter`           | Generic up/down counter with overflow detection | active       |
| `generic_LFSR_8bit` | 8-bit linear feedback shift register (LFSR)     | *deprecated* |
| `lfsr_8bit`         | 8-bit linear feedback shift register (LFSR)     | active       |
| `lfsr_16bit`        | 16-bit linear feedback shift register (LFSR)    | active       |
| `mv_filter`         | **ZARUBAF ADD DESCRIPTION**                     | active       |

### Data Path Elements

|         Name        |                                 Description                                  |    Status    |
|---------------------|------------------------------------------------------------------------------|--------------|
| `binary_to_gray`    | Binary to gray code converter                                                | active       |
| `find_first_one`    | Leading-one finder / leading-zero counter                                    | *deprecated* |
| `gray_to_binary`    | Gray code to binary converter                                                | active       |
| `lzc`               | Leading/trailing-zero counter                                                | active       |
| `onehot_to_bin`     | One-hot to binary converter                                                  | active       |
| `pipe_reg_simple`   | Pipeline register for arbitrary types                                        | active       |
| `rrarbiter`         | Round-robin arbiter for req/ack interface with look-ahead                    | active       |
| `spill_register`    | Register with ready/valid interface to cut all combinational interface paths | active       |
| `stream_arbiter`    | Round-robin arbiter for ready/valid stream interface                         | active       |
| `stream_demux`      | Ready/valid interface demultiplexer                                          | active       |
| `stream_mux`        | Ready/valid interface multiplexer                                            | active       |
| `stream_register`   | Register with ready/valid interface                                          | active       |
| `ready_valid_delay` | Randomize or delay ready/valid interface                                     | active       |
| `popcount`          | Combinatorial popcount (hamming weight)                                      | active       |

### Data Structures

|        Name        |                  Description                  |    Status    |
|--------------------|-----------------------------------------------|--------------|
| `fifo`             | FIFO register with upper threshold            | *deprecated* |
| `fifo_v2`          | FIFO register with upper and lower threshold  | *deprecated* |
| `fifo_v3`          | FIFO register with generic fill counts        | active       |
| `generic_fifo`     | FIFO register without thresholds              | *deprecated* |
| `generic_fifo_adv` | FIFO register without thresholds              | *deprecated* |
| `sram`             | SRAM behavioral model                         | active       |
| `unread`           | Empty module to sink unconnected outputs into | active       |


## Header Contents

This repository currently contains the following header files.

### Register Header

The register header file `register_defines.svh` contains macros that expand to descriptions of registers.
To avoid misuse of `always_ff` blocks, only the following macros shall be used to describe sequential behavior.
The use of linter rules that flag explicit uses of `always_ff` in source code is encouraged.

|         Macro         |                            Arguments                            |                               Description                               |
|-----------------------|-----------------------------------------------------------------|-------------------------------------------------------------------------|
| <code>\`FF</code>     | `q_sig`, `d_sig`, `rst_val`                                     | Flip-flop with asynchronous active-low reset (implicit)                 |
| <code>\`FFAR</code>   | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `arst_sig`              | Flip-flop with asynchronous active-high reset                           |
| <code>\`FFARN</code>  | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `arstn_sig`             | Flip-flop with asynchronous active-low reset                            |
| <code>\`FFSR</code>   | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `rst_sig`               | Flip-flop with synchronous active-high reset                            |
| <code>\`FFSRN</code>  | `q_sig`, `d_sig`, `rst_val`, `clk_sig`, `rstn_sig`              | Flip-flop with synchronous active-low reset                             |
| <code>\`FFNR</code>   | `q_sig`, `d_sig`, `clk_sig`                                     | Flip-flop without reset                                                 |
|                       |                                                                 |                                                                         |
| <code>\`FFL</code>    | `q_sig`, `d_sig`, `load_ena`, `rst_val`                         | Flip-flop with load-enable and asynchronous active-low reset (implicit) |
| <code>\`FFLAR</code>  | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `arst_sig`  | Flip-flop with load-enable and asynchronous active-high reset           |
| <code>\`FFLARN</code> | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `arstn_sig` | Flip-flop with load-enable and asynchronous active-low reset            |
| <code>\`FFLSR</code>  | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `rst_sig`   | Flip-flop with load-enable and synchronous active-high reset            |
| <code>\`FFLSRN</code> | `q_sig`, `d_sig`, `load_ena`, `rst_val`, `clk_sig`, `rstn_sig`  | Flip-flop with load-enable and synchronous active-low reset             |
| <code>\`FFLNR</code>  | `q_sig`, `d_sig`, `load_ena`, `clk_sig`                         | Flip-flop with load-enable without reset                                |
- *The name of the clock and reset signals for implicit variants is `clk_i` and `rst_ni`, respectively.*
- *Argument suffix `_sig` indicates signal names for present and next state as well as clocks and resets.*
- *Argument `rst_val` specifies the value literal to be assigned upon reset.*
- *Argument `load_ena` specifies the boolean expression that forms the load enable of the register.*
