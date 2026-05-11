/-
  Verity.Macro.KeccakLit: compile-time Keccak-256 literal sugar.

  Exposes pure helpers that turn UTF-8 string literals into their
  Keccak-256 hash interpreted as a 256-bit big-endian word.  These are
  intended for use inside `constants` (and other pure positions) in
  `verity_contract` bodies, where a stable namespace key is needed —
  e.g. ERC-7201-style storage namespaces, EIP-712 domain separators,
  event topic constants, and the like.

  Both helpers are total Lean definitions backed by `Verity.KeccakEngine.keccak256_str`
  (the in-tree pure Keccak engine, shipped via #1416 / #1683).  No new
  trust assumption is introduced — the hash is computed at elaboration
  time, not via an EVM precompile call.
-/

import Compiler.Keccak.Sponge
import Verity.Core

namespace Verity

/-- Compile-time Keccak-256 of a UTF-8 encoded string literal, returned as
    a `Nat` in big-endian word order.  Suitable for direct comparison with
    `Uint256` storage slots and for constants.

    Thin re-export of `KeccakEngine.keccak256_str_nat` so EDSL authors can
    refer to the helper from the public `Verity` namespace. -/
def keccak256_nat (s : String) : Nat :=
  KeccakEngine.keccak256_str_nat s

/-- Compile-time Keccak-256 of a UTF-8 encoded string literal, returned as
    a `Uint256`.  This is the canonical way to express ERC-7201-style
    storage namespace constants inside a `verity_contract` body:

    ```
    constants
      STORAGE_NAMESPACE : Uint256 := keccak256_lit "MyContract.storage.v0"
    ```
-/
def keccak256_lit (s : String) : Uint256 :=
  Verity.Core.Uint256.ofNat (keccak256_nat s)

/-! ### Compile-time correctness vectors

These checks guarantee that the sugar matches the official Keccak-256
test vectors and that the result fits inside `Uint256` without
modular reduction (the hash is always 256 bits). -/

set_option maxRecDepth 100000 in
theorem keccak256_nat_empty :
    keccak256_nat "" =
      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  native_decide

set_option maxRecDepth 100000 in
theorem keccak256_lit_empty_val :
    (keccak256_lit "").val =
      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  native_decide

end Verity

