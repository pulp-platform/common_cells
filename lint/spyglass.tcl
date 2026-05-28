new_project $env(IP) -force
current_methodology $env(SPYGLASS_HOME)/GuideWare/latest/block/rtl_handoff

read_file -type sourcelist analyze.tcl

set_option enableSV09 yes
set_option allow_module_override yes
set_option designread_disable_flatten no
set_option nopreserve yes

waive -rules CMD_define02 -msg "*TARGET_FLIST*"

set result [compile_design -top $env(IP)]
set code [lindex $result 0]
exit -force $code
