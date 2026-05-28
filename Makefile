BENDER    ?= bender
VERILATOR ?= verilator

# All modules in src/ with a top-level module declaration, minus skipped ones
SV_MODULES   = $(patsubst src/%.sv,%,$(shell grep -l "^module " src/*.sv))
ELAB_TARGETS = $(addprefix elab-,$(SV_MODULES))

.PHONY: all elab $(ELAB_TARGETS)

all: elab

# Re-run bender checkout only when Bender.yml changes
.bender/.checkout: Bender.yml
	$(BENDER) checkout
	@touch $@

elab: $(ELAB_TARGETS)

$(ELAB_TARGETS): elab-%: .bender/.checkout
	$(VERILATOR) --cc \
		$(shell $(BENDER) script verilator -t rtl) \
		--top-module $* \
		-Wno-fatal \
		-j $(shell nproc)
