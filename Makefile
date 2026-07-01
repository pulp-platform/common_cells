BENDER    ?= bender
VERILATOR ?= verilator
VSIM      ?= vsim
VCS_SEPP  ?=
SG_SHELL  ?= sg_shell

# Suppress vlog-2583: always_comb/always_latch conflict checks are deferred to vopt
VLOG_FLAGS += -suppress 2583

VSIM_BUILDDIR = $(abspath build/vsim)
VCS_BUILDDIR  = $(abspath build/vcs)
SG_BUILDDIR   = $(abspath build/spyglass)

# All modules in src/ with a top-level module declaration, minus skipped ones
SV_MODULES       = $(patsubst src/%.sv,%,$(shell grep -l "^module " src/*.sv))
VLT_ELAB_TARGETS = $(addprefix vlt-elab-,$(SV_MODULES))
SG_LINT_TARGETS  = $(addprefix sg-lint-,$(SV_MODULES))

.PHONY: all vlt-elab $(VLT_ELAB_TARGETS) vsim-elab vcs-elab sg-lint $(SG_LINT_TARGETS) clean

all: vlt-elab vsim-elab vcs-elab sg-lint

# Re-run bender checkout only when Bender.yml changes
.bender/.checkout: Bender.yml
	$(BENDER) checkout
	@touch $@

vlt-elab: $(VLT_ELAB_TARGETS)

$(VLT_ELAB_TARGETS): vlt-elab-%: .bender/.checkout
	$(VERILATOR) --cc \
		$(shell $(BENDER) script verilator) \
		--top-module $* \
		-Wno-IMPLICIT \
		-Wno-UNSIGNED \
		-Wno-WIDTHEXPAND \
		-Wno-WIDTHTRUNC \
		-Wno-UNOPTFLAT \
		-Wno-MULTIDRIVEN \
		-j $(shell nproc)

$(VSIM_BUILDDIR) $(VCS_BUILDDIR) $(SG_BUILDDIR):
	mkdir -p $@

$(VSIM_BUILDDIR)/elaborate.tcl: Bender.yml | $(VSIM_BUILDDIR) .bender/.checkout
	$(BENDER) script vsim --vlog-arg="$(VLOG_FLAGS) " > $@

vsim-elab: $(VSIM_BUILDDIR)/elaborate.tcl
	cd $(VSIM_BUILDDIR) && $(VSIM) -c -do "source $<; quit"

$(VCS_BUILDDIR)/elaborate.sh: Bender.yml | $(VCS_BUILDDIR) .bender/.checkout
	$(BENDER) script vcs > $@
	chmod +x $@

vcs-elab: $(VCS_BUILDDIR)/elaborate.sh
	cd $(VCS_BUILDDIR) && $(VCS_SEPP) $<

$(SG_BUILDDIR)/analyze.tcl: Bender.yml | $(SG_BUILDDIR) .bender/.checkout
	$(BENDER) script flist-plus > $@

sg-lint: $(SG_LINT_TARGETS)

$(SG_LINT_TARGETS): sg-lint-%: $(SG_BUILDDIR)/analyze.tcl
	cd $(SG_BUILDDIR) && IP=$* $(SG_SHELL) -enable_pass_exit_codes -tcl $(abspath lint/spyglass.tcl)

clean:
	rm -rf build/
