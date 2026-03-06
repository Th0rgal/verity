import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EventAbiHelpers
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.IssueRefs

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def encodeStaticCustomErrorArg (errorName : String) (ty : ParamType) (argExpr : YulExpr) :
    Except String YulExpr :=
  match ty with
  | ParamType.uint256 | ParamType.bytes32 =>
      pure argExpr
  | ParamType.uint8 =>
      pure (YulExpr.call "and" [argExpr, YulExpr.lit 255])
  | ParamType.address =>
      pure (YulExpr.call "and" [argExpr, YulExpr.hex addressMask])
  | ParamType.bool =>
      pure (yulToBool argExpr)
  | _ =>
      throw s!"Compilation error: custom error '{errorName}' uses unsupported non-scalar parameter type {repr ty} in scalar encoding ({issue586Ref})."

/-- Compute the ABI head size (in bytes) for a list of member types.
Static members take their flattened word count × 32; dynamic members take 32 (offset word). -/
def abiHeadSize (tys : List ParamType) : Nat :=
  tys.foldl (fun acc ty => acc + eventHeadWordSize ty) 0

/-- Recursively ABI-encode a dynamic composite type into memory at `dstBase`.
    Reads input from `dynamicSource` at `srcBase`.
    Returns `(stmts, totalLenExpr)` where `totalLenExpr` is the total bytes written. -/
partial def compileUnindexedAbiEncode
    (dynamicSource : DynamicDataSource) (ty : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    Except String (List YulStmt × YulExpr) := do
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      let loaded := dynamicWordLoad dynamicSource srcBase
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
      ], YulExpr.lit 32)
  | ParamType.bytes =>
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      pure ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
        YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      ] ++ dynamicCopyData dynamicSource
        (YulExpr.call "add" [dstBase, YulExpr.lit 32])
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident lenName
          ],
          YulExpr.lit 0
        ])
      ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])
  | ParamType.tuple elemTys =>
      let headSize := abiHeadSize elemTys
      let tailLenName := s!"{stem}_tail_len"
      let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
      let rec goMembers (remaining : List ParamType) (elemIdx headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | elemTy :: rest =>
            let elemSrcName := s!"{stem}_m{elemIdx}_src"
            let elemDstName := s!"{stem}_m{elemIdx}_dst"
            let srcStmts :=
              if eventIsDynamicType elemTy then
                let relName := s!"{stem}_m{elemIdx}_rel"
                [
                  YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                    srcBase, YulExpr.lit headOffset
                  ])),
                  YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
                ]
              else
                [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
            let encStmts ←
              if eventIsDynamicType elemTy then do
                let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.call "add" [dstBase, YulExpr.lit headOffset],
                  YulExpr.ident tailLenName
                ])
                let (innerStmts, innerLen) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.ident elemDstName)
                    s!"{stem}_m{elemIdx}"
                pure ([storeOffset,
                  YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
                ] ++ innerStmts ++ [
                  YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
                ])
              else do
                let (innerStmts, _) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.call "add" [dstBase, YulExpr.lit headOffset])
                    s!"{stem}_m{elemIdx}"
                pure innerStmts
            let restStmts ← goMembers rest (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
            pure (srcStmts ++ encStmts ++ restStmts)
      let memberStmts ← goMembers elemTys 0 0
      pure (initStmts ++ memberStmts, YulExpr.ident tailLenName)
  | ParamType.fixedArray elemTy n =>
      if eventIsDynamicType elemTy then
        let tailLenName := s!"{stem}_fa_tail_len"
        let headSize := n * 32
        let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
        let rec goElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let elemDstName := s!"{stem}_fa{i}_dst"
            let relName := s!"{stem}_fa{i}_rel"
            let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [dstBase, YulExpr.lit (i * 32)],
              YulExpr.ident tailLenName
            ])
            let srcStmts := [
              YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                srcBase, YulExpr.lit (i * 32)
              ])),
              YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
            ]
            let (innerStmts, innerLen) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.ident elemDstName)
                s!"{stem}_fa{i}"
            let restStmts ← goElems (i + 1)
            pure (srcStmts ++ [storeOffset,
              YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
            ] ++ innerStmts ++ [
              YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
            ] ++ restStmts)
          else
            pure []
        let elemStmts ← goElems 0
        pure (initStmts ++ elemStmts, YulExpr.ident tailLenName)
      else
        let elemWordSize := eventHeadWordSize elemTy
        let rec goStaticElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let srcStmt := YulStmt.let_ elemSrcName (YulExpr.call "add" [
              srcBase, YulExpr.lit (i * elemWordSize)
            ])
            let (innerStmts, _) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.call "add" [dstBase, YulExpr.lit (i * elemWordSize)])
                s!"{stem}_fa{i}"
            let restStmts ← goStaticElems (i + 1)
            pure ([srcStmt] ++ innerStmts ++ restStmts)
          else
            pure []
        let elemStmts ← goStaticElems 0
        pure (elemStmts, YulExpr.lit (n * elemWordSize))
  | ParamType.array elemTy =>
      let lenName := s!"{stem}_arr_len"
      let lenStmt := YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      let storeLenStmt := YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      if eventIsDynamicType elemTy then
        let headLenName := s!"{stem}_arr_head_len"
        let tailLenName := s!"{stem}_arr_tail_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemRelName := s!"{stem}_arr_elem_rel"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let elemDstName := s!"{stem}_arr_elem_dst"
        let (innerStmts, innerLen) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.ident elemDstName)
            s!"{stem}_arr_e"
        let loopBody := [
          YulStmt.let_ elemRelName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
          ])),
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.ident elemRelName
          ]),
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
            ],
            YulExpr.ident tailLenName
          ]),
          YulStmt.let_ elemDstName (YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident tailLenName
          ])
        ] ++ innerStmts ++ [
          YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
        ]
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        pure ([lenStmt, storeLenStmt,
          YulStmt.let_ headLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit 32]),
          YulStmt.let_ tailLenName (YulExpr.ident headLenName),
          loopStmt
        ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident tailLenName])
      else
        let elemWordSize := eventHeadWordSize elemTy
        let byteLenName := s!"{stem}_arr_byte_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let (innerStmts, _) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
            ])
            s!"{stem}_arr_e"
        let loopBody := [
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
          ])
        ] ++ innerStmts
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        let paddedName := s!"{stem}_arr_padded"
        pure ([lenStmt, storeLenStmt,
            YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
            loopStmt,
            YulStmt.let_ paddedName (YulExpr.call "and" [
              YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
              YulExpr.call "not" [YulExpr.lit 31]
            ])
          ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])

def revertWithCustomError (dynamicSource : DynamicDataSource)
    (errorDef : ErrorDef) (sourceArgs : List Expr) (args : List YulExpr) :
    Except String (List YulStmt) := do
  if errorDef.params.length != args.length || sourceArgs.length != args.length then
    throw s!"Compilation error: custom error '{errorDef.name}' expects {errorDef.params.length} args, got {args.length}"
  let sigBytes := bytesFromString (errorSignature errorDef)
  let storePtr := YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
  let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
      YulExpr.hex (wordFromBytes chunk)
    ])
  let hashStmt := YulStmt.let_ "__err_hash"
    (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr", YulExpr.lit sigBytes.length])
  let selectorStmt := YulStmt.let_ "__err_selector"
    (YulExpr.call "shl" [YulExpr.lit selectorShift, YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]])
  let selectorStore := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "__err_selector"])
  let headSize := abiHeadSize errorDef.params
  let tailInit := YulStmt.let_ "__err_tail" (YulExpr.lit headSize)
  let argsWithSources := (errorDef.params.zip sourceArgs).zip args |>.map (fun ((ty, srcExpr), argExpr) => (ty, srcExpr, argExpr))
  let rec attachOffsets (items : List (ParamType × Expr × YulExpr)) (headOffset : Nat) :
      List (ParamType × Expr × YulExpr × Nat) :=
    match items with
    | [] => []
    | (ty, srcExpr, argExpr) :: rest =>
        (ty, srcExpr, argExpr, headOffset) :: attachOffsets rest (headOffset + paramHeadSize ty)
  let argsWithHeadOffsets := attachOffsets argsWithSources 4
  let argStores ← argsWithHeadOffsets.zipIdx.mapM fun ((ty, srcExpr, argExpr, headOffset), idx) => do
    match ty with
    | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        let encoded ← encodeStaticCustomErrorArg errorDef.name ty argExpr
        pure [YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, encoded])]
    | ParamType.tuple _ | ParamType.fixedArray _ _ =>
        match srcExpr with
        | Expr.param name =>
            if isDynamicParamType ty then
              let dstName := s!"__err_arg{idx}_dst"
              let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
              let (encStmts, encLen) ←
                compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
              pure ([
                YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
                YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
              ] ++ encStmts ++ [
                YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
              ])
            else
              let leaves := staticCompositeLeaves name ty
              let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.lit (headOffset + wordIdx * 32),
                  normalizeEventWord leafTy leafExpr
                ])
              pure stores
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
    | ParamType.bytes | ParamType.array _ =>
        match srcExpr with
        | Expr.param name =>
            let dstName := s!"__err_arg{idx}_dst"
            let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
            let (encStmts, encLen) ←
              compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
            pure ([
              YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
              YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
            ] ++ encStmts ++ [
              YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
            ])
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
  let revertStmt := YulStmt.expr (YulExpr.call "revert" [
    YulExpr.lit 0,
    YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]
  ])
  pure [YulStmt.block ([storePtr] ++ sigStores ++ [hashStmt, selectorStmt, selectorStore, tailInit] ++ argStores.flatten ++ [revertStmt])]

end Compiler.CompilationModel
