# User config
set ::env(DESIGN_NAME) RISC_SPM

# Change if needed
set ::env(VERILOG_FILES) [glob $::env(DESIGN_DIR)/../../verilog/rtl/risc_spm/src/*.v]

set ::env(DESIGN_IS_CORE) 0


set ::env(CLOCK_PERIOD) "100.0"
set ::env(CLOCK_PORT) "clk"

set ::env(FP_SIZING) absolute
set ::env(DIE_AREA) "0 0 1000 1000"

set ::env(PL_BASIC_PLACEMENT) 0
set ::env(PL_TARGET_DENSITY) 0.2

set ::env(RT_MAX_LAYER) {met4}

# You can draw more power domains if you need to 
set ::env(VDD_NETS) [list {vccd1}]
set ::env(GND_NETS) [list {vssd1}]

set ::env(DIODE_INSERTION_STRATEGY) 4 

set ::env(RUN_CVC) 1
