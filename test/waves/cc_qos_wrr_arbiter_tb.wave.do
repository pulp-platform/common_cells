onerror {resume}
quietly WaveActivateNextPane {} 0

# Testbench-level signals (phase, req/gnt, QoS, weights, output handshake, idx, data)
add wave -noupdate -group {tb} {/cc_qos_wrr_arbiter_tb/*}

# QoS stage: aging counters, effective QoS and the winning tier.
add wave -noupdate -group {qos} {/cc_qos_wrr_arbiter_tb/i_dut/*}

# Weighted round-robin stage: burst counter and contender snapshot.
add wave -noupdate -group {wrr} {/cc_qos_wrr_arbiter_tb/i_dut/i_cc_wrr_arbiter/*}

# Inner fair round-robin tree used purely as a winner picker.
add wave -noupdate -group {inner_rr} {/cc_qos_wrr_arbiter_tb/i_dut/i_cc_wrr_arbiter/i_cc_rr_arb_tree/*}

TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
configure wave -namecolwidth 200
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
# Zoom to the first few hundred ns so the per-winner bursts are visible.
WaveRestoreZoom {0 ns} {500 ns}
