new_project $env(IP) -force
current_methodology $env(SPYGLASS_HOME)/GuideWare/latest/block/rtl_handoff

read_file -type sourcelist analyze.tcl

set_option top $env(IP)
set_option enableSV09 yes
set_option allow_module_override yes
set_option designread_disable_flatten no
set_option nopreserve yes

# Ignore unused macro definition automatically defined by bender.
waive -rules CMD_define02 -msg "*TARGET_FLIST*"
# Ignore multiple assignments in always_comb block, which is common e.g. with default assignments.
waive -rules W415a
# Suppress warning on variables that are set but not read. It is common e.g. to have variables that
# are only used in assertions.
waive -rules W528
# Allow unconnected outputs
waive -rules W287b
# In certain IPs, there are intentional blocking assignments in always_ff blocks
if {$env(IP) in {cc_clk_int_div cc_clk_int_div_static}} {
    waive -rules W336
}
# Ignore if clock enable pin is always enabled/disabled
waive -rules FlopEConst
# Suppress warning on inputs that are declared but not read. It is common e.g. to have inputs that
# are only used in certain parameterizations.
waive -rules W240

set result [run_goal -goal lint/lint_rtl]
set code [lindex $result 0]

exit -force $code
