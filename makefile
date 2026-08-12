AGDA_FILES := $(shell find . -name '*.agda' -not -path './_build/*' | sort)

.PHONY: default clean audit

default:
	agda Everything.agda

clean:
	rm -rf _build

# The development cannot be typechecked with --safe, because it uses
# --sized-types. This target is a mechanical substitute: it lists
# every feature in the development that --safe would reject, so that
# the inventory can be checked rather than taken on trust.
audit:
	@echo "== OPTIONS pragmas =="
	@grep -h '{-# OPTIONS' $(AGDA_FILES) | sed 's/^[[:space:]]*//' | sort | uniq -c
	@echo
	@echo "== postulates =="
	@grep -nE '^[[:space:]]*postulate([[:space:]]|$$)' $(AGDA_FILES) || echo "(none)"
	@echo
	@echo "== pragmas that switch off a soundness check =="
	@grep -nE '\{-#[[:space:]]*(TERMINATING|NON_TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_TERMINATION_CHECK|NO_UNIVERSE_CHECK|POLARITY|INJECTIVE|REWRITE)' $(AGDA_FILES) || echo "(none)"
	@echo
	@echo "== uses of trustMe =="
	@grep -nE 'trustMe' $(AGDA_FILES) || echo "(none)"
