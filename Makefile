# ── Top-level build for the libsignal-theory demos ───────────────────────────
# Pipeline per demo:
#   demos/rust/*.rs  --Charon-->  *.llbc  --Aeneas-->  demos/lean/Demos/Extracted/*.lean
#   --Lake + VCVio-->  machine-checked security proof.
#
# Generated files (.llbc and Demos/Extracted/*.lean) are NOT committed; `make`
# regenerates them. Requires the local toolchain in deps/ (see README.md).

AENEAS_DIR ?= deps/aeneas
CHARON     := $(AENEAS_DIR)/charon/bin/charon
AENEAS     := $(AENEAS_DIR)/bin/aeneas

PROJ       := demos/lean
RUST       := demos/rust
EXTRACTED  := $(PROJ)/Demos/Extracted
SCRATCH    := $(PROJ)/.build

.PHONY: all build verify extract clean check-deps

all: build

## Fail early with a helpful message if the local toolchain isn't built.
check-deps:
	@test -x "$(CHARON)" || { echo "ERROR: missing $(CHARON) — build the local toolchain first (see README.md)."; exit 1; }
	@test -x "$(AENEAS)" || { echo "ERROR: missing $(AENEAS) — build the local toolchain first (see README.md)."; exit 1; }

## Regenerate the extracted Lean models from the Rust sources.
extract: check-deps
	@mkdir -p "$(EXTRACTED)" "$(SCRATCH)"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/otp.llbc"    -- $(RUST)/otp.rs    --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/otp.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/stream.llbc" -- $(RUST)/stream.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/stream.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/ratchet.llbc" -- $(RUST)/ratchet.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/ratchet.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/chacha.llbc" -- $(RUST)/chacha.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/chacha.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/pqxdh.llbc" -- $(RUST)/pqxdh/pqxdh.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/pqxdh.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/gf.llbc" -- $(RUST)/spqr/gf.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/gf.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/authenticator.llbc" -- $(RUST)/spqr/authenticator.rs --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/authenticator.llbc"
	$(CHARON) rustc --preset=aeneas --dest-file "$(SCRATCH)/mac.llbc"    -- $(RUST)/mac.rs    --crate-type=lib
	$(AENEAS) -backend lean -dest "$(EXTRACTED)" "$(SCRATCH)/mac.llbc"

## Extract, then type-check every demo (Mathlib oleans via `lake exe cache get`).
build: extract
	cd $(PROJ) && lake exe cache get >/dev/null 2>&1 || true
	cd $(PROJ) && lake build

## Build, then gate on the axiom set: every headline theorem must depend ONLY on the
## three standard axioms — no sorry, no native_decide, no custom axioms (see scripts/audit.sh).
verify: build
	@bash scripts/audit.sh

## Remove generated artifacts (keeps the Lake/Mathlib build cache).
clean:
	rm -rf "$(EXTRACTED)" "$(SCRATCH)"
