# SPDX-License-Identifier: GPL-3.0-only
# Copyright (c) 2023 CERN
#
# Please retain this header in all redistributions and modifications of the code.

cmake_minimum_required(VERSION 3.25)
project(common_cells NONE)

# Fetch dependencies
include("deps/deps.cmake")

add_ip(common_cells
    VENDOR pulp_platform
    LIBRARY ip
    VERSION 1.33.1
)

# include/common_cells/registers.svh
# include/common_cells/assertions.svh
ip_include_directories(${IP} SYSTEMVERILOG
    ${PROJECT_SOURCE_DIR}/include/common_cells
)

ip_sources(${IP} SYSTEMVERILOG
    # Source files grouped in levels. Files in level 0 have no dependencies on files in this
    # package. Files in level 1 only depend on files in level 0, files in level 2 on files in
    # levels 1 and 0, etc. Files within a level are ordered alphabetically.
    # Level 0
    ${PROJECT_SOURCE_DIR}/src/cdc_reset_ctrlr_pkg.sv
    # ${PROJECT_SOURCE_DIR}/src/binary_to_gray.sv
    # ${PROJECT_SOURCE_DIR}/src/cb_filter_pkg.sv
    # ${PROJECT_SOURCE_DIR}/src/cc_onehot.sv
    # ${PROJECT_SOURCE_DIR}/src/cf_math_pkg.sv
    # ${PROJECT_SOURCE_DIR}/src/clk_int_div.sv
    ${PROJECT_SOURCE_DIR}/src/delta_counter.sv
    # ${PROJECT_SOURCE_DIR}/src/ecc_pkg.sv
    # ${PROJECT_SOURCE_DIR}/src/edge_propagator_tx.sv
    # ${PROJECT_SOURCE_DIR}/src/exp_backoff.sv
    ${PROJECT_SOURCE_DIR}/src/fifo_v3.sv
    # ${PROJECT_SOURCE_DIR}/src/gray_to_binary.sv
    # ${PROJECT_SOURCE_DIR}/src/isochronous_4phase_handshake.sv
    # ${PROJECT_SOURCE_DIR}/src/isochronous_spill_register.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/lfsr.sv
    # ${PROJECT_SOURCE_DIR}/src/lfsr_16bit.sv
    # ${PROJECT_SOURCE_DIR}/src/lfsr_8bit.sv
    # ${PROJECT_SOURCE_DIR}/src/multiaddr_decode.sv # not compiling standalone xcelium
    # ${PROJECT_SOURCE_DIR}/src/mv_filter.sv
    # ${PROJECT_SOURCE_DIR}/src/onehot_to_bin.sv
    # ${PROJECT_SOURCE_DIR}/src/plru_tree.sv
    # ${PROJECT_SOURCE_DIR}/src/passthrough_stream_fifo.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/popcount.sv
    ${PROJECT_SOURCE_DIR}/src/rr_arb_tree.sv
    # ${PROJECT_SOURCE_DIR}/src/rstgen_bypass.sv
    # ${PROJECT_SOURCE_DIR}/src/serial_deglitch.sv
    # ${PROJECT_SOURCE_DIR}/src/shift_reg.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/shift_reg_gated.sv # unsupported 'parameter type' by TMRG
    ${PROJECT_SOURCE_DIR}/src/spill_register_flushable.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_demux.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_filter.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_fork.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_intf.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_join.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_join_dynamic.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_mux.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_throttle.sv
    # ${PROJECT_SOURCE_DIR}/src/sub_per_hash.sv
    ${PROJECT_SOURCE_DIR}/src/sync.sv
    # ${PROJECT_SOURCE_DIR}/src/sync_wedge.sv # Reference to pulp_clock_gating (not defined)
    # ${PROJECT_SOURCE_DIR}/src/unread.sv
    # ${PROJECT_SOURCE_DIR}/src/read.sv
    # Level 1
    ${PROJECT_SOURCE_DIR}/src/addr_map_rule_pkg.sv
    ${PROJECT_SOURCE_DIR}/src/addr_decode_dync.sv
    # ${PROJECT_SOURCE_DIR}/src/cdc_2phase.sv
    ${PROJECT_SOURCE_DIR}/src/cdc_4phase.sv
    # ${PROJECT_SOURCE_DIR}/src/cb_filter.sv
    # ${PROJECT_SOURCE_DIR}/src/cdc_fifo_2phase.sv
    ${PROJECT_SOURCE_DIR}/src/counter.sv
    # ${PROJECT_SOURCE_DIR}/src/ecc_decode.sv
    # ${PROJECT_SOURCE_DIR}/src/ecc_encode.sv
    # ${PROJECT_SOURCE_DIR}/src/edge_detect.sv # Reference so sync_wedge
    ${PROJECT_SOURCE_DIR}/src/lzc.sv
    # ${PROJECT_SOURCE_DIR}/src/max_counter.sv
    # ${PROJECT_SOURCE_DIR}/src/rstgen.sv
    ${PROJECT_SOURCE_DIR}/src/spill_register.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_delay.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_fifo.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_fork_dynamic.sv
    # ${PROJECT_SOURCE_DIR}/src/clk_mux_glitch_free.sv
    # Level 2
    ${PROJECT_SOURCE_DIR}/src/addr_decode.sv
    # ${PROJECT_SOURCE_DIR}/src/addr_decode_napot.sv
    ${PROJECT_SOURCE_DIR}/src/cdc_reset_ctrlr.sv
    # ${PROJECT_SOURCE_DIR}/src/cdc_fifo_gray.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/fall_through_register.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/id_queue.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_to_mem.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_arbiter_flushable.sv # not compiling standalone xcelium
    # ${PROJECT_SOURCE_DIR}/src/stream_fifo_optimal_wrap.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_register.sv # unsupported 'parameter type' by TMRG
    # ${PROJECT_SOURCE_DIR}/src/stream_xbar.sv # unsupported 'parameter type' by TMRG
    # Level 3
    # ${PROJECT_SOURCE_DIR}/src/cdc_fifo_gray_clearable.sv
    ${PROJECT_SOURCE_DIR}/src/cdc_2phase_dst_clearable.sv
    ${PROJECT_SOURCE_DIR}/src/cdc_2phase_src_clearable.sv
    ${PROJECT_SOURCE_DIR}/src/cdc_2phase_clearable.sv
    # ${PROJECT_SOURCE_DIR}/src/mem_to_banks_detailed.sv
    # ${PROJECT_SOURCE_DIR}/src/stream_arbiter.sv # not compiling standalone xcelium
    # ${PROJECT_SOURCE_DIR}/src/stream_omega_net.sv
    # Level 4
    # ${PROJECT_SOURCE_DIR}/src/mem_to_banks.sv

    # Deprecated modules
    # Level 0
    # ${PROJECT_SOURCE_DIR}/src/deprecated/clock_divider_counter.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/clk_div.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/find_first_one.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/generic_LFSR_8bit.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/generic_fifo.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/prioarbiter.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/pulp_sync.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/pulp_sync_wedge.sv
    # ${PROJECT_SOURCE_DIR}/src/deprecated/rrarbiter.sv
    # Level 1
    # ${PROJECT_SOURCE_DIR}/src/deprecated/clock_divider.sv
    ${PROJECT_SOURCE_DIR}/src/deprecated/fifo_v2.sv
    # Level 2
    # ${PROJECT_SOURCE_DIR}/src/deprecated/fifo_v1.sv

    # Depend on deprecated modules
    # ${PROJECT_SOURCE_DIR}/src/edge_propagator_ack.sv
    # ${PROJECT_SOURCE_DIR}/src/edge_propagator.sv
    # ${PROJECT_SOURCE_DIR}/src/edge_propagator_rx.sv
)

ip_link(${IP} pulp_platform::ip::tech_cells_generic)

if(NOT PROJECT_IS_TOP_LEVEL)
    set(RTL_LIB_NAME ${IP} PARENT_SCOPE)
endif()
