# explain.md - Verity Audit Explorer Spec

Status: Draft implementation spec
Owner: Community / ecosystem (separate repo)
Related: #122

## Purpose

Define a concrete, buildable MVP for an explorer that turns Verity proofs into human-readable audit reports.

This is not part of the core prover/compiler pipeline. It is a downstream consumer of Verity artifacts and should live in a dedicated repository (for example `Th0rgal/verity-audit`).

## Problem

Verity can prove strong properties, but those guarantees are hard to discover and compare across contracts. Users need a structured report that answers:

1. What is proven?
2. What is still trusted?
3. What is not proven yet?

## Product Surface

Input:
- A known Verity contract identity (initially from a curated registry)

Output:
- A deterministic audit report page + JSON payload with:
  - Source reference (repo + commit)
  - Build/proof status (`lake build`, theorem counts, `sorry` count)
  - Proven guarantees (theorem-backed)
  - Trust assumptions (axioms + boundary notes)
  - Not-proven section

## Scope (Phase 1)

In scope:
- Curated contract registry (start with bundled Verity examples)
- CI pipeline that clones Verity at pinned commit and extracts verification metadata
- Static report generation (JSON)
- Static site renderer for report pages

Out of scope:
- Permissionless repo submissions
- On-chain bytecode matching
- Wallet/block-explorer API integrations

## Report JSON Schema (v0)

```json
{
  "schemaVersion": "v0",
  "contract": {
    "name": "SimpleToken",
    "repo": "https://github.com/Th0rgal/verity",
    "commit": "<git-sha>",
    "sourcePath": "Verity/Examples/SimpleToken.lean"
  },
  "verification": {
    "lakeBuildPass": true,
    "theoremCount": 0,
    "axiomCount": 0,
    "sorryCount": 0
  },
  "guarantees": [
    {
      "id": "simpleToken_owner_only_mint",
      "theorem": "mint_only_owner",
      "summary": "Only the owner can mint new tokens.",
      "status": "proven"
    }
  ],
  "trustAssumptions": [
    {
      "id": "solc_yul_to_bytecode",
      "source": "TRUST_ASSUMPTIONS.md",
      "summary": "Yul to bytecode correctness depends on solc."
    }
  ],
  "notProven": [
    "ERC20 full standard compliance"
  ]
}
```

## Extraction Rules

The extractor should be deterministic and fail closed:

1. Pin exact Verity commit.
2. Run `lake build` in CI.
3. Count:
   - theorems
   - axioms
   - `sorry`
4. Reject report generation if `lake build` fails.
5. Mark any non-zero `sorry` as `verificationStatus: partial`.

## Repository Boundaries

Verity repo responsibilities:
- Keep proof artifacts and trust-assumption docs machine-readable enough for extraction.

Audit explorer repo responsibilities:
- Registry management
- Extraction pipeline
- JSON generation
- Web UI/API

## Minimal Milestones

1. Define final JSON schema and add schema validation.
2. Generate reports for current example contracts.
3. Publish static site with one page per contract.
4. Add CI gate to regenerate reports and detect drift.

## Success Criteria

- A newcomer can open a report and answer within 30 seconds:
  - What is mathematically proven?
  - What is still trusted?
  - Is the proof complete (`sorryCount == 0`)?
- Report generation is reproducible from `(repo, commit)` with no manual edits.
- Output is stable enough for downstream consumers (wallets, explorers, agents).

## Future Phases

Phase 2:
- Self-service verification for arbitrary Git repositories (sandboxed builds)

Phase 3:
- Permissionless on-chain bytecode matching and provenance linking

Phase 4:
- API integrations and verifier badges for external tooling
