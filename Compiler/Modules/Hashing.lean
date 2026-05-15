/-
  Compiler.Modules.Hashing: packed static hash helpers

  These helpers cover common audit-modeling hash preimages:
  - static 32-byte words
  - static byte-width segments from 1 to 32 bytes

  They intentionally do not model dynamic Solidity packed encoding for bytes or
  strings yet.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Hashing

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

private def packedWordTempName (idx : Nat) : String :=
  s!"__packed_word_{idx}"

private def packedWordBindings (words : List YulExpr) : List YulStmt :=
  words.zipIdx.map fun (word, idx) =>
    YulStmt.let_ (packedWordTempName idx) word

private def packedWordTempStores (wordCount : Nat) : List YulStmt :=
  (List.range wordCount).map fun idx =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit (idx * 32),
      YulExpr.ident (packedWordTempName idx)
    ])

private def alignUp32 (n : Nat) : Nat :=
  ((n + 31) / 32) * 32

private def packedSegmentMask (width : Nat) : Nat :=
  2 ^ (width * 8) - 1

private def packedSegmentTempStore (offset width idx : Nat) : YulStmt :=
  let value := YulExpr.ident (packedWordTempName idx)
  let stored :=
    if width == 32 then
      value
    else
      YulExpr.call "shl" [
        YulExpr.lit ((32 - width) * 8),
        YulExpr.call "and" [value, YulExpr.hex (packedSegmentMask width)]
      ]
  YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, stored])

private def packedSegmentTempStoresAux (offset : Nat) : List Nat → Nat → List YulStmt
  | [], _ => []
  | width :: widths, idx =>
      packedSegmentTempStore offset width idx ::
        packedSegmentTempStoresAux (offset + width) widths (idx + 1)

private def packedSegmentTempStores (widths : List Nat) : List YulStmt :=
  packedSegmentTempStoresAux 0 widths 0

private def validatePackedSegmentWidths (moduleName : String) (widths : List Nat) : Except String Unit :=
  widths.forM fun width =>
    if width == 0 || width > 32 then
      throw s!"{moduleName} segment widths must be between 1 and 32 bytes"
    else
      pure ()

/-- Keccak-256 over packed static 32-byte words stored at scratch memory offset 0.
    This is the static-word subset of Solidity `abi.encodePacked(...)` followed
    by `keccak256`. -/
def abiEncodePackedWordsModule (resultVar : String) (wordCount : Nat) : ExternalCallModule where
  name := "abiEncodePackedWords"
  numArgs := wordCount
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_packed_static_word_layout"]
  compile := fun _ctx args => do
    if args.length != wordCount then
      throw s!"abiEncodePackedWords expects {wordCount} static word argument(s)"
    let size := wordCount * 32
    pure [
      YulStmt.block (packedWordBindings args ++ packedWordTempStores wordCount),
      YulStmt.let_ resultVar (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit size])
    ]

/-- Convenience constructor for static-word packed Keccak hashing. -/
def abiEncodePackedWords (resultVar : String) (words : List Expr) : Stmt :=
  .ecm (abiEncodePackedWordsModule resultVar words.length) words

/-- Short alias for the static 32-byte-word subset of `abi.encodePacked`.
    Use `abiEncodePackedWords` when the narrower semantics should be explicit at
    the call site. -/
def abiEncodePacked (resultVar : String) (words : List Expr) : Stmt :=
  abiEncodePackedWords resultVar words

/-- Keccak-256 over Solidity `abi.encode(array)` for a direct dynamic-array
    parameter whose elements have a fixed static word width.

    The module takes the array length as its single expression argument and
    references `{arrayParam}_data_offset` emitted by the calldata/internal
    dynamic-array lowering. It encodes the single dynamic-array argument as:

      head offset (32), array length, contiguous static element words

    This covers arrays such as `uint256[]`, `address[]`, and arrays of static
    tuples/structs when the caller supplies the element word width. -/
def abiEncodeStaticArrayModule
    (resultVar arrayParam : String) (elementWords : Nat) : ExternalCallModule where
  name := "abiEncodeStaticArray"
  numArgs := 1
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_standard_dynamic_array_static_element_layout"]
  compile := fun ctx args => do
    let arrayLengthExpr ←
      match args with
      | [arrayLengthExpr] => pure arrayLengthExpr
      | _ => throw s!"abiEncodeStaticArray expects 1 expression argument, got {args.length}"
    if arrayParam.isEmpty then
      throw "abiEncodeStaticArray requires a non-empty array parameter name"
    if elementWords == 0 then
      throw "abiEncodeStaticArray requires elementWords > 0"
    let ptrName := s!"__{resultVar}_abi_array_ptr"
    let dataBytesName := s!"__{resultVar}_abi_array_data_bytes"
    let totalBytesName := s!"__{resultVar}_abi_array_total_bytes"
    let paddedTotalName := s!"__{resultVar}_abi_array_padded_total"
    let ptr := YulExpr.ident ptrName
    let dataBytes := YulExpr.ident dataBytesName
    let totalBytes := YulExpr.ident totalBytesName
    pure [
      YulStmt.block ([
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.expr (YulExpr.call "mstore" [ptr, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 32],
          arrayLengthExpr
        ]),
        YulStmt.let_ dataBytesName (YulExpr.call "mul" [
          arrayLengthExpr,
          YulExpr.lit (elementWords * 32)
        ])
      ] ++ ECM.dynamicCopyData ctx
        (YulExpr.call "add" [ptr, YulExpr.lit 64])
        (YulExpr.ident s!"{arrayParam}_data_offset")
        dataBytes ++ [
        YulStmt.let_ totalBytesName (YulExpr.call "add" [YulExpr.lit 64, dataBytes]),
        YulStmt.let_ paddedTotalName (YulExpr.call "and" [
          YulExpr.call "add" [totalBytes, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptr, YulExpr.ident paddedTotalName]
        ]),
        YulStmt.let_ resultVar (YulExpr.call "keccak256" [ptr, totalBytes])
      ])
    ]

/-- Convenience constructor for `keccak256(abi.encode(array))` over static-width
    dynamic-array parameters. -/
def abiEncodeStaticArray
    (resultVar arrayParam : String) (elementWords : Nat) (arrayLength : Expr) : Stmt :=
  .ecm (abiEncodeStaticArrayModule resultVar arrayParam elementWords) [arrayLength]

/-- Keccak-256 over packed static byte-width segments.
    Each argument is encoded as exactly the matching byte width from `widths`,
    using Solidity's left-aligned memory representation for sub-word static
    values. Sub-word values are masked to their requested width before being
    shifted into position. Widths must be between 1 and 32 bytes. -/
def abiEncodePackedStaticSegmentsModule (resultVar : String) (widths : List Nat) : ExternalCallModule where
  name := "abiEncodePackedStaticSegments"
  numArgs := widths.length
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_packed_static_segment_layout"]
  compile := fun _ctx args => do
    if args.length != widths.length then
      throw s!"abiEncodePackedStaticSegments expects {widths.length} static segment argument(s)"
    validatePackedSegmentWidths "abiEncodePackedStaticSegments" widths
    let size := widths.foldl (· + ·) 0
    pure [
      YulStmt.block (packedWordBindings args ++ packedSegmentTempStores widths),
      YulStmt.let_ resultVar (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit size])
    ]

/-- Convenience constructor for static byte-width packed Keccak hashing. -/
def abiEncodePackedStaticSegments (resultVar : String) (segments : List (Expr × Nat)) : Stmt :=
  .ecm (abiEncodePackedStaticSegmentsModule resultVar (segments.map Prod.snd))
    (segments.map Prod.fst)

/-- SHA-256 over packed static 32-byte words stored at scratch memory offset 0.
    The digest is written after the packed input words and then bound from
    memory, avoiding overlap with the preimage. -/
def sha256PackedWordsModule (resultVar : String) (wordCount : Nat) : ExternalCallModule where
  name := "sha256PackedWords"
  numArgs := wordCount
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_sha256_precompile", "abi_packed_static_word_layout"]
  compile := fun _ctx args => do
    if args.length != wordCount then
      throw s!"sha256PackedWords expects {wordCount} static word argument(s)"
    let size := wordCount * 32
    let outputOffset := size
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 2,
      YulExpr.lit 0, YulExpr.lit size,
      YulExpr.lit outputOffset, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sha256_packed_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    pure [
      YulStmt.block (packedWordBindings args ++ packedWordTempStores wordCount ++ [
        YulStmt.let_ "__sha256_packed_success" callExpr,
        revertBlock
      ]),
      YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit outputOffset])
    ]

/-- Convenience constructor for static-word packed SHA-256 hashing. -/
def sha256PackedWords (resultVar : String) (words : List Expr) : Stmt :=
  .ecm (sha256PackedWordsModule resultVar words.length) words

/-- Short alias for static 32-byte-word packed SHA-256 preimages. -/
def sha256Packed (resultVar : String) (words : List Expr) : Stmt :=
  sha256PackedWords resultVar words

/-- SHA-256 over packed static byte-width segments.
    The digest is written at the next 32-byte-aligned offset after the preimage
    to avoid overlapping with non-word-sized packed input bytes. Sub-word
    values are masked to their requested width before being shifted into
    position. -/
def sha256PackedStaticSegmentsModule (resultVar : String) (widths : List Nat) : ExternalCallModule where
  name := "sha256PackedStaticSegments"
  numArgs := widths.length
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_sha256_precompile", "abi_packed_static_segment_layout"]
  compile := fun _ctx args => do
    if args.length != widths.length then
      throw s!"sha256PackedStaticSegments expects {widths.length} static segment argument(s)"
    validatePackedSegmentWidths "sha256PackedStaticSegments" widths
    let size := widths.foldl (· + ·) 0
    let outputOffset := alignUp32 size
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 2,
      YulExpr.lit 0, YulExpr.lit size,
      YulExpr.lit outputOffset, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sha256_packed_segments_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    pure [
      YulStmt.block (packedWordBindings args ++ packedSegmentTempStores widths ++ [
        YulStmt.let_ "__sha256_packed_segments_success" callExpr,
        revertBlock
      ]),
      YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit outputOffset])
    ]

/-- Convenience constructor for static byte-width packed SHA-256 hashing. -/
def sha256PackedStaticSegments (resultVar : String) (segments : List (Expr × Nat)) : Stmt :=
  .ecm (sha256PackedStaticSegmentsModule resultVar (segments.map Prod.snd))
    (segments.map Prod.fst)

end Compiler.Modules.Hashing
