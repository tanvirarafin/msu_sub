# User config
set ::env(DESIGN_NAME) RISC_SPM

# Change if needed
set ::env(VERILOG_FILES) [glob $::env(DESIGN_DIR)/../../verilog/rtl/risc_spm/*.v]

# Fill this
# Fill this

set ::env(CLOCK_PERIOD) "100.0"
set ::env(CLOCK_PORT) "clk"

set ::env(PL_TARGET_DENSITY) "0.52"
set ::env(GLB_RT_ADJUSTMENT) "0.2"
set ::env(FP_CORE_UTIL) "50"



set filename $::env(DESIGN_DIR)/$::env(PDK)_$::env(STD_CELL_LIBRARY)_config.tcl
if { [file exists $filename] == 1} {
	source $filename
}

