# SPDX-FileCopyrightText: 2020 Efabless Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0


 
PWDD := $(shell pwd)
BLOCKS := $(shell basename $(PWDD))

# ---- Include Partitioned Makefiles ----

CONFIG = caravel_user_project


export COCOTB_REDUCED_LOG_FMT=1
export PYTHONPATH := $(DESIGNS)/verilog/rtl/risc_spm/tests/
export LIBPYTHON_LOC=$(shell cocotb-config --libpython)

include $(MCW_ROOT)/verilog/dv/make/env.makefile
include $(MCW_ROOT)/verilog/dv/make/var.makefile
include $(MCW_ROOT)/verilog/dv/make/cpu.makefile
include $(MCW_ROOT)/verilog/dv/make/sim.makefile




coco_test: risc_spm.hex
	rm -rf sim_build/
	mkdir sim_build/

	iverilog -Ttyp -DFUNCTIONAL -DSIM -DUSE_POWER_PINS -DUNIT_DELAY=#1 \
	-f$(VERILOG_PATH)/includes/includes.rtl.caravel \
	-f$(USER_PROJECT_VERILOG)/includes/includes.rtl.$(CONFIG) -o sim_build/sim.vvp risc_spm_tb.v

	TESTCASE=test_start,test_all MODULE=test_risc_spm vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
	! grep failure results.xml

coco_test_gl: risc_spm.hex
	rm -rf sim_build/
	mkdir sim_build/

	iverilog -Ttyp -DFUNCTIONAL -DSIM -DUSE_POWER_PINS -DUNIT_DELAY=#1 \
	-f$(VERILOG_PATH)/includes/includes.rtl.caravel \
	-f$(USER_PROJECT_VERILOG)/includes/includes.gl.$(CONFIG) -o sim_build/sim.vvp risc_spm_tb.v

	TESTCASE=test_start,test_all_gl MODULE=test_risc_spm vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
	! grep failure results.xml
