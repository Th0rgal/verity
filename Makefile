# Verity: Formally verified smart contracts
#
# Prerequisites: curl, git, python3, bash
# Run `make setup` to install all tooling, then `make verify` to check all proofs.

.PHONY: help setup setup-elan setup-solc setup-foundry \
        verify test test-foundry test-python axiom-report \
        compile generate-yul check ci-fast ci-fast-build \
        refresh-status install-fast-hook all clean

# Pinned versions (must match .github/workflows/verify.yml)
ELAN_VERSION     := v4.1.2
SOLC_VERSION     := 0.8.33
SOLC_URL         := https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v$(SOLC_VERSION)+commit.64118f21
SOLC_SHA256      := 1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468
FOUNDRY_VERSION  := v1.5.0

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-20s\033[0m %s\n", $$1, $$2}'

# ---------------------------------------------------------------------------
# Setup
# ---------------------------------------------------------------------------

setup: setup-elan setup-solc setup-foundry ## Install all tooling (elan, solc, foundry)
	@echo ""
	@echo "Setup complete. Run 'make verify' to check all proofs."

setup-elan: ## Install elan + Lean toolchain
	@if command -v elan >/dev/null 2>&1; then \
		echo "elan already installed: $$(elan --version)"; \
	else \
		echo "Installing elan $(ELAN_VERSION)..."; \
		curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/$(ELAN_VERSION)/elan-init.sh" | \
			bash -s -- -y --default-toolchain none; \
		echo 'Add $$HOME/.elan/bin to your PATH if not already present.'; \
	fi

setup-solc: ## Install solc (SHA256-verified)
	@if command -v solc >/dev/null 2>&1 && solc --version 2>/dev/null | grep -q "$(SOLC_VERSION)"; then \
		echo "solc $(SOLC_VERSION) already installed"; \
	else \
		echo "Installing solc $(SOLC_VERSION)..."; \
		curl -sSfL "$(SOLC_URL)" -o /tmp/solc; \
		echo "$(SOLC_SHA256)  /tmp/solc" | sha256sum -c -; \
		sudo mv /tmp/solc /usr/local/bin/solc; \
		sudo chmod +x /usr/local/bin/solc; \
		echo "solc $(SOLC_VERSION) installed"; \
	fi

setup-foundry: ## Install Foundry (forge, cast, anvil)
	@if command -v forge >/dev/null 2>&1; then \
		echo "Foundry already installed: $$(forge --version)"; \
	else \
		echo "Installing Foundry $(FOUNDRY_VERSION)..."; \
		curl -L https://foundry.paradigm.xyz | bash; \
		$$HOME/.foundry/bin/foundryup --version $(FOUNDRY_VERSION); \
		echo 'Add $$HOME/.foundry/bin to your PATH if not already present.'; \
	fi

# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

verify: ## Verify all proofs (lake build)
	lake build

axiom-report: ## Generate axiom dependency report for all 569 theorems
	lake env lean PrintAxioms.lean 2>&1 | tee axiom-report-raw.log
	python3 scripts/check_axiom_report.py --log axiom-report-raw.log

# ---------------------------------------------------------------------------
# Compilation
# ---------------------------------------------------------------------------

compile: ## Build compiler + interpreter
	lake build verity-compiler difftest-interpreter

generate-yul: compile ## Compile all contracts to Yul
	./.lake/build/bin/verity-compiler

# ---------------------------------------------------------------------------
# Testing
# ---------------------------------------------------------------------------

test: test-python ## Run fast tests (Python validators)

test-python: ## Run Python unit tests (140 tests, ~4s)
	python3 -m unittest discover -s scripts -p 'test_*.py' -v

test-foundry: ## Run Foundry differential tests (requires solc + forge + generated Yul)
	FOUNDRY_PROFILE=difftest forge test

check: ## Run all CI validation scripts (no Lean build required)
	@echo "Running CI validation scripts..."
	python3 scripts/check_property_manifest.py
	python3 scripts/check_property_coverage.py
	python3 scripts/check_contract_structure.py
	python3 scripts/check_axiom_locations.py
	python3 scripts/check_doc_counts.py
	python3 scripts/check_lean_hygiene.py
	python3 scripts/generate_print_axioms.py --check
	@echo "All checks passed."

ci-fast: ## Fast local gate for issue #1060 progress runs (no Lean build)
	scripts/run_1060_fast_gate.sh

ci-fast-build: ## Fast local gate + Lean build for issue #1060 progress runs
	scripts/run_1060_fast_gate.sh --with-build

refresh-status: ## Regenerate verification artifact and auto-fix doc counts
	scripts/refresh_verification_artifacts.sh

install-fast-hook: ## Install a pre-push hook that runs the issue #1060 fast gate
	scripts/install_pre_push_fast_gate.sh

# ---------------------------------------------------------------------------
# Full pipeline
# ---------------------------------------------------------------------------

all: verify check test-python axiom-report ## Full local verification pipeline
	@echo ""
	@echo "All proofs verified, all checks passed, axiom report generated."

clean: ## Remove build artifacts
	lake clean
	rm -f axiom-report-raw.log axiom-report.md
