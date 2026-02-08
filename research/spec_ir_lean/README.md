# Spec IR + Lean Sketch

This folder is a minimal, non-executable sketch of a Lean-backed proof path for the
"dumb contracts" DSL. The idea is to keep a tiny Spec IR and prove the checker
for that IR is sound.

Goals
- Define a minimal Spec IR (requires, ensures, modifies, invariants).
- Give the IR a formal semantics in Lean.
- Prove the checker is sound (if the checker accepts a transition, it satisfies
  the IR semantics).
- Keep the Solidity harness generator as an engineering bridge until we have a
  semantics-level proof for the EVM execution model.

Notes
- This is a sketch. It is not wired into a Lean toolchain yet.
- We expect to add an executable checker function later and prove the connection
  between the generated harness and the IR semantics.
