import Contracts.Common
import Compiler.CheckContract
import Contracts.Counter.Counter
import Contracts.SimpleStorage.SimpleStorage
import Contracts.Owned.Owned
import Contracts.SafeCounter.SafeCounter
import Contracts.OwnedCounter.OwnedCounter
import Contracts.Ledger.Ledger
import Contracts.Vault.Vault
import Contracts.SimpleToken.SimpleToken
import Contracts.ERC20.ERC20
import Contracts.ERC721.ERC721
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

private def genericECMEffectDemoModule : Compiler.ECM.ExternalCallModule where
  name := "genericEffectDemo"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

verity_contract UintMapSmoke where
  storage
    values : Uint256 → Uint256 := slot 0

  function setValue (key : Uint256, value : Uint256) : Unit := do
    setMappingUint values key value

  function getValue (key : Uint256) : Uint256 := do
    let current ← getMappingUint values key
    return current

verity_contract MappingChainSmoke where
  storage
    approvals : Address → Address → Address → Uint256 := slot 0

  function setApproval (owner : Address, spender : Address, delegate_ : Address, value : Uint256) : Unit := do
    setMappingN approvals [owner, spender, delegate_] value

  function getApproval (owner : Address, spender : Address, delegate_ : Address) : Uint256 := do
    let current ← getMappingN approvals [owner, spender, delegate_]
    return current

verity_contract MixedMappingChainSmoke where
  storage
    approvals : Address → Uint256 → Address → Uint256 := slot 0

  function setApproval (owner : Address, tokenId : Uint256, delegate_ : Address, value : Uint256) : Unit := do
    setMappingN approvals [addressToWord owner, tokenId, addressToWord delegate_] value

  function getApproval (owner : Address, tokenId : Uint256, delegate_ : Address) : Uint256 := do
    let current ← getMappingN approvals [addressToWord owner, tokenId, addressToWord delegate_]
    return current

verity_contract Bytes32Smoke where
  storage
    value : Uint256 := slot 0

  function setDigest (digest : Bytes32) : Unit := do
    setStorage value digest

  function getDigest () : Bytes32 := do
    let digest ← getStorage value
    return digest

verity_contract StorageArraySmoke where
  storage
    queue : Array Uint256 := slot 0

  function size () : Uint256 := do
    let size ← getStorageArrayLength queue
    return size

  function push (value : Uint256) : Unit := do
    pushStorageArray queue value

/--
error: field 'queue' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement
-/
#guard_msgs in
verity_contract StorageArraySetStorageUnsupported where
  storage
    queue : Array Uint256 := slot 0

  function badWrite (value : Uint256) : Unit := do
    setStorage queue value

/--
error: field 'queue' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement
-/
#guard_msgs in
verity_contract StorageArraySetStorageAddrUnsupported where
  storage
    queue : Array Uint256 := slot 0

  function badWrite (owner : Address) : Unit := do
    setStorageAddr queue owner

verity_contract MappingWordSmoke where
  storage
    words : Uint256 → Uint256 := slot 0

  function setWord1 (key : Uint256, value : Uint256) : Unit := do
    setMappingWord words key 1 value

  function getWord1 (key : Uint256) : Uint256 := do
    let word ← getMappingWord words key 1
    return word

  function isWord1NonZero (key : Uint256) : Bool := do
    let word ← getMappingWord words key 1
    return (word != 0)

verity_contract StorageWordsSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bytes32) : Array Uint256 := do
    returnStorageWords slots

/--
error: returnStorageWords requires an Array Bytes32 or Array Uint256 parameter on the compilation-model path, got Verity.Macro.ValueType.array (Verity.Macro.ValueType.address)
-/
#guard_msgs in
verity_contract StorageWordsUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Address) : Array Uint256 := do
    returnStorageWords slots

/--
error: returnStorageWords currently requires a direct parameter reference on the compilation-model path
-/
#guard_msgs in
verity_contract StorageWordsConstructedUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (_ok : Bool, slots : Array Bytes32) : Array Uint256 := do
    returnStorageWords ([] : Array Bytes32)

/--
error: returnArray currently requires a direct parameter reference on the compilation-model path
-/
#guard_msgs in
verity_contract ReturnArrayConstructedUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function echo (_ok : Bool, values : Array Uint256) : Array Uint256 := do
    returnArray ([] : Array Uint256)

verity_contract CustomErrorSmoke where
  storage
    sentinel : Uint256 := slot 0

  errors
    error NonPositive(Uint256)
    error AmountTooLarge(Uint256, Uint256)

  function echo (amount : Uint256) : Uint256 := do
    return amount

verity_contract SignedBuiltinSmoke where
  storage

  constants
    extendedByte : Uint256 := (signextend 0 255)
    arithmeticShifted : Uint256 := (sar 255 (sub 0 1))
    negativeOne : Int256 := (toInt256 (sub 0 1))

  function signedDiv (lhs : Uint256, rhs : Uint256) : Uint256 := do
    return (sdiv lhs rhs)

  function signedMod (lhs : Uint256, rhs : Uint256) : Uint256 := do
    return (smod lhs rhs)

  function signedLt (lhs : Uint256, rhs : Uint256) : Bool := do
    return (slt lhs rhs)

  function signedGt (lhs : Uint256, rhs : Uint256) : Bool := do
    return (sgt lhs rhs)

  function arithmeticShift (shift : Uint256, value : Uint256) : Uint256 := do
    return (sar shift value)

  function signExtended () : Uint256 := do
    return extendedByte

  function shiftedMask () : Uint256 := do
    return arithmeticShifted

  function signedDivSurface (lhs : Int256, rhs : Int256) : Int256 := do
    return (lhs / rhs)

  function signedModSurface (lhs : Int256, rhs : Int256) : Int256 := do
    return (lhs % rhs)

  function signedDivViaLocal (raw : Uint256, denom : Int256) : Int256 := do
    let signedRaw := toInt256 raw
    return (signedRaw / denom)

  function castToInt (value : Uint256) : Int256 := do
    return (toInt256 value)

  function castToUint (value : Int256) : Uint256 := do
    return (toUint256 value)

  function minusOne () : Int256 := do
    return negativeOne

/--
error: unsigned word arithmetic does not support Int256 operands; cast to Uint256 explicitly first
-/
#guard_msgs in
verity_contract SignedMinRejected where
  storage

  function badMin (lhs : Int256) : Int256 := do
    return (min lhs 0)

verity_contract StatelessSmoke where
  storage

  function echoWord (value : Uint256) : Uint256 := do
    return value

  function whoAmI () : Address := do
    let sender ← msgSender
    return sender

verity_contract MutabilitySmoke where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function payable deposit () : Uint256 := do
    let value ← msgValue
    return value

  function view currentOwner () : Address := do
    let ownerAddr ← getStorageAddr owner
    return ownerAddr

verity_contract SpecialEntrypointSmoke where
  storage
    receiveCount : Uint256 := slot 0
    fallbackCount : Uint256 := slot 1

  receive := do
    let current ← getStorage receiveCount
    setStorage receiveCount (add current 1)

  fallback := do
    let current ← getStorage fallbackCount
    setStorage fallbackCount (add current 1)

  function getReceiveCount () : Uint256 := do
    let current ← getStorage receiveCount
    return current

  function getFallbackCount () : Uint256 := do
    let current ← getStorage fallbackCount
    return current

verity_contract ConstantSmoke where
  storage

  constants
    basisPoints : Uint256 := 10000
    mintFeeBps : Uint256 := 30
    treasury : Address := (wordToAddress 42)

  function feeOn (amount : Uint256) : Uint256 := do
    let fee := div (mul amount mintFeeBps) basisPoints
    return fee

  function treasuryAddr () : Address := do
    return treasury

verity_contract ImmutableSmoke where
  storage
    owner : Address := slot 0

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := (add seed offset)
    treasury : Address := ownerSeed

  constructor (seed : Uint256, ownerSeed : Address) := do
    setStorageAddr owner ownerSeed

  function supplyCap () : Uint256 := do
    return seededSupply

  function treasuryAddr () : Address := do
    return treasury

  function shadowed (seededSupply : Uint256) : Uint256 := do
    return seededSupply

verity_contract TypedImmutableSmoke where
  storage

  immutables
    paused : Bool := true
    feeBps : Uint8 := 7
    domainTag : Bytes32 := 42

  function isPaused () : Bool := do
    return paused

  function feeScale () : Uint8 := do
    return feeBps

  function domainSeparator () : Bytes32 := do
    return domainTag

verity_contract InitializerSmoke where
  storage
    initializedVersion : Uint256 := slot 0
    owner : Address := slot 1
    paused : Uint256 := slot 2

  function initOwner (seedOwner : Address) initializer(initializedVersion) : Unit := do
    setStorageAddr owner seedOwner

  function upgradeToV2 () reinitializer(initializedVersion, 2) : Unit := do
    setStorage paused 1

/--
error: initializer guard field 'owner' must be a Uint256 storage slot
-/
#guard_msgs in
verity_contract InitializerGuardFieldTypeRejected where
  storage
    owner : Address := slot 0

  function initOwner () initializer(owner) : Unit := do
    pure ()

/--
error: reinitializer version must be greater than 0
-/
#guard_msgs in
verity_contract InitializerZeroVersionRejected where
  storage
    initializedVersion : Uint256 := slot 0

  function upgradeToV0 () reinitializer(initializedVersion, 0) : Unit := do
    pure ()

/--
error: contract constants must be compile-time expressions; 'blobbasefee' is runtime-dependent
-/
#guard_msgs in
verity_contract ConstantRuntimeBuiltinRejected where
  storage

  constants
    seededAt : Uint256 := blobbasefee

  function seeded () : Uint256 := do
    return seededAt

/--
 error: contract immutables currently support only Uint256, Int256, Uint8, Address, Bytes32, and Bool; 'metadata' uses unsupported type
-/
#guard_msgs in
verity_contract ImmutableTypeRejected where
  storage

  immutables
    metadata : String := "paused"

  function metadataWord () : Uint256 := do
    return 0

/--
error: immutable 'fee' expects Verity.Macro.ValueType.uint256, got Verity.Macro.ValueType.bool
-/
#guard_msgs in
verity_contract ImmutableBoolAssignedToWordRejected where
  storage

  immutables
    fee : Uint256 := true

  function feeWord () : Uint256 := do
    return fee

/--
error: immutable 'owner' expects Verity.Macro.ValueType.address, got Verity.Macro.ValueType.bool
-/
#guard_msgs in
verity_contract ImmutableBoolAssignedToAddressRejected where
  storage

  immutables
    owner : Address := true

  function ownerAddr () : Address := do
    return owner

/--
error: immutable 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract ImmutableStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  immutables
    owner : Address := zeroAddress

  function getOwner () : Address := do
    return owner

/--
error: immutable 'basisPoints' conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ImmutableConstantNameConflictRejected where
  storage

  constants
    basisPoints : Uint256 := 10000

  immutables
    basisPoints : Uint256 := 9999

  function getBasisPoints () : Uint256 := do
    return basisPoints

/--
error: duplicate immutable declaration 'seededSupply'
-/
#guard_msgs in
verity_contract DuplicateImmutableRejected where
  storage

  immutables
    seededSupply : Uint256 := 1
    seededSupply : Uint256 := 2

  function getSeededSupply () : Uint256 := do
    return seededSupply

/--
error: duplicate storage field declaration 'owner'
-/
#guard_msgs in
verity_contract DuplicateStorageFieldRejected where
  storage
    owner : Address := slot 0
    owner : Address := slot 1

  function getOwner () : Address := do
    return zeroAddress

/--
error: constant 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract ConstantStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  constants
    owner : Uint256 := 1

  function ownerWord () : Uint256 := do
    return owner

/--
error: duplicate constant declaration 'basisPoints'
-/
#guard_msgs in
verity_contract DuplicateConstantRejected where
  storage

  constants
    basisPoints : Uint256 := 10000
    basisPoints : Uint256 := 9999

  function getBasisPoints () : Uint256 := do
    return basisPoints

/--
error: function 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract FunctionStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  function owner () : Address := do
    return zeroAddress

/--
error: function 'fee' conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract FunctionConstantNameConflictRejected where
  storage

  constants
    fee : Uint256 := 7

  function fee () : Uint256 := do
    return 0

/--
error: duplicate function declaration 'echo'
-/
#guard_msgs in
verity_contract DuplicateFunctionRejected where
  storage

  function echo () : Uint256 := do
    return 1

  function echo () : Uint256 := do
    return 2

/--
error: storage field 'spec' conflicts with reserved generated declaration 'spec'
-/
#guard_msgs in
verity_contract ReservedSpecStorageNameRejected where
  storage
    spec : Address := slot 0

  function owner () : Address := do
    return zeroAddress

/--
error: function 'settle_model' conflicts with reserved generated declaration 'settle_model'
-/
#guard_msgs in
verity_contract FunctionGeneratedHelperNameRejected where
  storage

  function settle () : Uint256 := do
    return 1

  function settle_model () : Uint256 := do
    return 2

/--
error: function 'price' generates helper 'price_model' that conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ConstantFunctionHelperCollisionRejected where
  storage

  constants
    price_model : Uint256 := 7

  function price () : Uint256 := do
    return 3

verity_contract TupleSmoke where
  storage
    values : Uint256 → Uint256 := slot 0
    authorized : Address → Uint256 := slot 1

  function setFromPair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let _pairValue := pair
    let key := pair_0
    let value := pair_1
    setMappingUint values key value

  function getPair (key : Uint256) : Tuple [Uint256, Uint256] := do
    return (key, key)

  function processConfig (cfg : Tuple [Address, Address, Uint256]) : Unit := do
    let _cfgValue := cfg
    let owner := cfg_0
    let _delegate := cfg_1
    let flag := cfg_2
    setMapping authorized owner flag

verity_contract Uint8Smoke where
  storage
    sentinel : Uint256 := slot 0

  function acceptSig (sig : Tuple [Uint8, Bytes32, Bytes32]) : Unit := do
    let _sigValue := sig
    let v := sig_0
    let _r := sig_1
    let _s := sig_2
    setStorage sentinel v

  function sigV () : Uint8 := do
    return 27

verity_contract AddressHelpersSmoke where
  storage
    delegates : Address → Uint256 := slot 0
    ownersById : Uint256 → Uint256 := slot 1

  function setDelegate (owner : Address, delegate : Address) : Unit := do
    setMappingAddr delegates owner delegate

  function getDelegate (owner : Address) : Address := do
    let delegate ← getMappingAddr delegates owner
    return delegate

  function clearDelegate (owner : Address) : Unit := do
    setMappingAddr delegates owner zeroAddress

  function hasDelegate (owner : Address) : Bool := do
    let delegate ← getMappingAddr delegates owner
    return (delegate != zeroAddress)

  function isDelegateZero (owner : Address) : Bool := do
    let delegate ← getMappingAddr delegates owner
    return isZeroAddress delegate

  function setOwnerForId (tokenId : Uint256, owner : Address) : Unit := do
    require (owner != zeroAddress) "Invalid owner"
    setMappingUintAddr ownersById tokenId owner

  function getOwnerForId (tokenId : Uint256) : Address := do
    let owner ← getMappingUintAddr ownersById tokenId
    return owner

verity_contract ZeroAddressShadowSmoke where
  storage
    delegates : Address → Uint256 := slot 0

  function shadowWrite (zeroAddress : Address) : Unit := do
    setMappingAddr delegates zeroAddress zeroAddress

verity_contract StructMappingSmoke where
  storage
    positions : MappingStruct(Address,[
      supplyShares @word 0 packed(0,128),
      borrowShares @word 0 packed(128,128),
      delegate @word 1
    ]) := slot 0
    approvals : MappingStruct2(Address,Address,[
      allowance @word 0 packed(0,128),
      nonce @word 1
    ]) := slot 1

  function setPosition (user : Address, supply : Uint256, borrow : Uint256, delegate_ : Address) : Unit := do
    setStructMember "positions" user "supplyShares" supply
    setStructMember "positions" user "borrowShares" borrow
    setStructMember "positions" user "delegate" delegate_

  function totalPositionShares (user : Address) : Uint256 := do
    let supply ← structMember "positions" user "supplyShares"
    let borrow ← structMember "positions" user "borrowShares"
    return (add supply borrow)

  function delegateOf (user : Address) : Address := do
    let delegate_ ← structMember "positions" user "delegate"
    return delegate_

  function setApproval (owner : Address, spender : Address, amount : Uint256, nextNonce : Uint256) : Unit := do
    setStructMember2 "approvals" owner spender "allowance" amount
    setStructMember2 "approvals" owner spender "nonce" nextNonce

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember2 "approvals" owner spender "allowance"
    return amount

  function approvalNonce (owner : Address, spender : Address) : Uint256 := do
    let nextNonce ← structMember2 "approvals" owner spender "nonce"
    return nextNonce

verity_contract ExternalCallSmoke where
  storage
    echoedValue : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function storeEcho (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage echoedValue echoed

  function getEchoedValue () : Uint256 := do
    let current ← getStorage echoedValue
    return current

verity_contract ERC20HelperSmoke where
  storage
    lastBalance : Uint256 := slot 0
    lastAllowance : Uint256 := slot 1
    lastSupply : Uint256 := slot 2

  function pushTokens (token : Address, to : Address, amount : Uint256) : Unit := do
    safeTransfer token to amount

  function pullTokens (token : Address, fromAddr : Address, to : Address, amount : Uint256) : Unit := do
    safeTransferFrom token fromAddr to amount

  function approveTokens (token : Address, spender : Address, amount : Uint256) : Unit := do
    safeApprove token spender amount

  function snapshotBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    setStorage lastBalance balance
    return balance

  function snapshotAllowance (token : Address, owner : Address, spender : Address) : Uint256 := do
    let current ← allowance token owner spender
    setStorage lastAllowance current
    return current

  function snapshotSupply (token : Address) : Uint256 := do
    let supply ← totalSupply token
    setStorage lastSupply supply
    return supply

verity_contract GenericECMReadSmoke where
  storage
    lastQuote : Uint256 := slot 0

  function snapshotQuote (oracle : Address, asset : Address) : Uint256 := do
    let quote ← ecmCall
      (fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)
      [oracle, asset]
    setStorage lastQuote quote
    return quote

verity_contract GenericECMWriteSmoke where
  storage

  function runEffect (lhs : Uint256, rhs : Uint256) : Unit := do
    ecmDo genericECMEffectDemoModule [lhs, rhs]

verity_contract LowLevelTryCatchSmoke where
  storage
    lastOutcome : Uint256 := slot 0

  function catchFailure ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 0 0 0 0 0) (do
      setStorage lastOutcome 7)
    let current ← getStorage lastOutcome
    return current

  function skipCatchOnSuccess ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 1 0 0 0 0 0 0) (do
      setStorage lastOutcome 9)
    let current ← getStorage lastOutcome
    return current

  function catchFailureWithShadowedParam (verity_try_success : Uint256)
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 0 0 0 0 0) (do
      setStorage lastOutcome 11)
    let current ← getStorage lastOutcome
    return current

/--
error: tryCatch catch payload 'err' is not available on the compilation-model path yet; use `_`/ignore it and read returndata explicitly if needed
-/
#guard_msgs in
verity_contract LowLevelTryCatchPayloadRejected where
  storage

  function badCatchPayload ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Unit
    := do
    tryCatch (call 0 0 0 0 0 0 0) (fun err => do
      require false err)

/--
error: ERC-20 helper form 'balanceOf' conflicts with contract function 'balanceOf'; rename the function or avoid the direct helper syntax here
-/
#guard_msgs in
verity_contract ERC20HelperShadowReadRejected where
  storage

  function balanceOf (token : Address, owner : Address) : Uint256 := do
    return (add (addressToWord token) (addressToWord owner))

  function readShadowedBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    return balance

/--
error: ERC-20 helper form 'safeTransfer' conflicts with contract function 'safeTransfer'; rename the function or avoid the direct helper syntax here
-/
#guard_msgs in
verity_contract ERC20HelperShadowWriteRejected where
  storage
    lastTransfer : Uint256 := slot 0

  function safeTransfer (_token : Address, _to : Address, amount : Uint256) : Unit := do
    setStorage lastTransfer amount

  function writeShadowedTransfer (token : Address, to : Address, amount : Uint256) : Unit := do
    safeTransfer token to amount

/--
 error: linked external 'describe' uses unsupported parameter type; executable externalCall currently supports only Uint256, Int256, Uint8, Address, Bytes32, and Bool
-/
#guard_msgs in
verity_contract ExternalCallUnsupportedType where
  storage
  linked_externals
    external describe(String) -> (Uint256)

  function noop () : Unit := do
    pure ()

/--
error: linked external 'fanout' currently supports at most one return value; statement-style external bindings are not exposed from verity_contract yet
-/
#guard_msgs in
verity_contract ExternalCallUnsupportedMultiReturn where
  storage
  linked_externals
    external fanout(Uint256) -> (Uint256, Address)

  function noop () : Unit := do
    pure ()

/--
error: ecmDo requires an effect-only ECM module, but 'oracleReadUint256' binds 1 result value(s)
-/
#guard_msgs in
verity_contract GenericECMDoRejectsResultModules where
  storage

  function badEffect (oracle : Address) : Uint256 := do
    ecmDo (Compiler.Modules.Oracle.oracleReadUint256Module "quote" 0x12345678 0) [oracle]
    return 0

/--
error: ecmCall must elaborate to an ECM module binding exactly ['quote'], but 'genericEffectDemo' binds []
-/
#guard_msgs in
verity_contract GenericECMCallRejectsEffectOnlyModules where
  storage

  function badBind (lhs : Uint256, rhs : Uint256) : Uint256 := do
    let quote ← ecmCall (fun _ => genericECMEffectDemoModule) [lhs, rhs]
    return quote

/--
error: unsupported proof status 'pending'; expected proved, assumed, or unchecked
-/
#guard_msgs in
verity_contract LocalObligationRejectsUnknownStatus where
  storage

  function badStatus () local_obligations [manual_check := pending "Must be proved later."] : Unit := do
    pure ()

/--
error: duplicate local obligation 'manual_check' on function 'unsafeEdge'
-/
#guard_msgs in
verity_contract LocalObligationRejectsDuplicateNames where
  storage

  function unsafeEdge () local_obligations [manual_check := assumed "First localized trust boundary.", manual_check := unchecked "Second localized trust boundary."] : Unit := do
    pure ()

/--
error: constructor local obligation 'manual_check' must not be empty
-/
#guard_msgs in
verity_contract LocalObligationRejectsEmptyConstructorMessage where
  storage

  constructor () local_obligations [manual_check := unchecked ""] := do
    pure ()

  function noop () : Unit := do
    pure ()

verity_contract LocalObligationRequiredForUnsafeFunctionBoundary where
  storage

  function preview () : Uint256 := do
    let head := calldataload 0
    return head

/--
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeFunctionBoundary': Compilation error: function 'preview' uses low-level/assembly mechanic(s) calldataload without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract LocalObligationRequiredForUnsafeFunctionBoundary

verity_contract LocalObligationRequiredForUnsafeConstructorBoundary where
  storage

  constructor () := do
    mstore 0 1
    pure ()

  function noop () : Unit := do
    pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeConstructorBoundary': Compilation error: constructor uses low-level/assembly mechanic(s) mstore without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract LocalObligationRequiredForUnsafeConstructorBoundary

/--
error: field 'approvals' is a nested struct mapping; use structMember2/setStructMember2
-/
#guard_msgs in
verity_contract StructMappingWrongReadAccessor where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember "approvals" owner "allowance"
    return amount

/--
error: field 'approvals' is a nested struct mapping; use structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongLegacyReadAccessor where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← getMapping2 approvals owner spender
    return amount

/--
error: field 'positions' is not a nested struct mapping
-/
#guard_msgs in
verity_contract StructMappingWrongWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setStructMember2 "positions" owner owner "delegate" delegate_

/--
error: field 'positions' is a struct-valued mapping; use setStructMember
-/
#guard_msgs in
verity_contract StructMappingWrongLegacyWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setMapping2 positions owner owner delegate_

/--
error: unknown struct member 'nonce' on field 'positions'
-/
#guard_msgs in
verity_contract StructMappingUnknownMember where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setNonce (owner : Address, value : Uint256) : Unit := do
    setStructMember "positions" owner "nonce" value

/--
error: field 'positions' is a struct-valued mapping; use structMember/structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongScalarReadAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function positionWord () : Uint256 := do
    let word ← getStorage positions
    return word

/--
error: field 'positions' is a struct-valued mapping; use structMember/structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongScalarAddressReadAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function delegateWord () : Address := do
    let word ← getStorageAddr positions
    return word

namespace SpecGenSmoke

#gen_spec storage_for2_spec for2 (x : Uint256) (y : Uint256)
  (0, (fun st => add (st.storage 0) (add x y)), Verity.Specs.sameAddrMapContext)

#gen_spec storage_for2_extra_spec for2 (x : Uint256) (y : Uint256)
  (0, (fun st => add (st.storage 0) (add x y)), Verity.Specs.sameAddrMapContext,
    (fun _ s' => s'.storage 0 >= x))

#gen_spec_addr addr_for2_spec for2 (owner : Address) (_salt : Uint256)
  (0, (fun _ => owner), Verity.Specs.sameStorageMapContext)

#gen_spec_addr addr_for2_extra_spec for2 (owner : Address) (salt : Uint256)
  (0, (fun _ => owner), Verity.Specs.sameStorageMapContext,
    (fun _ s' => s'.storage 0 = owner.toNat ∧ salt = salt))

#gen_spec_addr_storage addr_storage_for2_spec for2 (owner : Address) (value : Uint256)
  (0, 2, (fun _ => owner), (fun _ => value), Verity.Specs.sameStorageMapsContext)

#gen_spec_addr_storage addr_storage_for2_extra_spec for2 (owner : Address) (value : Uint256)
  (0, 2, (fun _ => owner), (fun _ => value), Verity.Specs.sameStorageMapsContext,
    (fun _ s' => s'.storage 2 = value))

example (x y : Uint256) (s s' : ContractState) :
    storage_for2_spec x y s s' =
      Verity.Specs.storageUpdateSpec 0 (fun st => add (st.storage 0) (add x y))
        Verity.Specs.sameAddrMapContext s s' := rfl

example (owner : Address) (salt : Uint256) (s s' : ContractState) :
    addr_for2_spec owner salt s s' =
      Verity.Specs.storageAddrUpdateSpec 0 (fun _ => owner)
        Verity.Specs.sameStorageMapContext s s' := rfl

example (owner : Address) (value : Uint256) (s s' : ContractState) :
    addr_storage_for2_spec owner value s s' =
      Verity.Specs.storageAddrStorageUpdateSpec 0 2 (fun _ => owner) (fun _ => value)
        Verity.Specs.sameStorageMapsContext s s' := rfl

end SpecGenSmoke

#check_contract Contracts.Counter
#check_contract UintMapSmoke
#check_contract Bytes32Smoke
#check_contract MappingWordSmoke
#check_contract StorageWordsSmoke
#check_contract CustomErrorSmoke
#check_contract SignedBuiltinSmoke
#check_contract StatelessSmoke
#check_contract SpecialEntrypointSmoke
#check_contract TupleSmoke
#check_contract Uint8Smoke
#check_contract AddressHelpersSmoke
#check_contract ZeroAddressShadowSmoke
#check_contract StructMappingSmoke
#check_contract ExternalCallSmoke
#check_contract Contracts.Vault

example : TupleSmoke.setFromPair = (TupleSmoke.setFromPair : (Uint256 × Uint256) → Verity.Contract Unit) := rfl
example : TupleSmoke.getPair = (TupleSmoke.getPair : Uint256 → Verity.Contract (Uint256 × Uint256)) := rfl
example :
    TupleSmoke.processConfig =
      (TupleSmoke.processConfig : (Address × Address × Uint256) → Verity.Contract Unit) := rfl
example : Uint8Smoke.acceptSig = (Uint8Smoke.acceptSig : (Uint256 × Uint256 × Uint256) → Verity.Contract Unit) := rfl
example : ExternalCallSmoke.storeEcho = (ExternalCallSmoke.storeEcho : Uint256 → Verity.Contract Unit) := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.increment_modelBody := by
  simpa using Contracts.Counter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.increment_modelBody := by
  simpa using Contracts.Counter.increment_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.decrement_modelBody := by
  simpa using Contracts.Counter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.decrement_modelBody := by
  simpa using Contracts.Counter.decrement_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.getCount_modelBody := by
  simpa using Contracts.Counter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.getCount_modelBody := by
  simpa using Contracts.Counter.getCount_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleStorage.store_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleStorage.store_modelBody := by
  simpa using Contracts.SimpleStorage.store_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleStorage.retrieve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleStorage.retrieve_modelBody := by
  simpa using Contracts.SimpleStorage.retrieve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Owned.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Owned.transferOwnership_modelBody := by
  simpa using Contracts.Owned.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Owned.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Owned.getOwner_modelBody := by
  simpa using Contracts.Owned.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.increment_modelBody := by
  simpa using Contracts.SafeCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.decrement_modelBody := by
  simpa using Contracts.SafeCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.getCount_modelBody := by
  simpa using Contracts.SafeCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.increment_modelBody := by
  simpa using Contracts.OwnedCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.decrement_modelBody := by
  simpa using Contracts.OwnedCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.getCount_modelBody := by
  simpa using Contracts.OwnedCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.getOwner_modelBody := by
  simpa using Contracts.OwnedCounter.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.transferOwnership_modelBody := by
  simpa using Contracts.OwnedCounter.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.deposit_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.deposit_modelBody := by
  simpa using Contracts.Ledger.deposit_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.withdraw_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.withdraw_modelBody := by
  simpa using Contracts.Ledger.withdraw_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.transfer_modelBody := by
  simpa using Contracts.Ledger.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.getBalance_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.getBalance_modelBody := by
  simpa using Contracts.Ledger.getBalance_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.mint_modelBody := by
  simpa using Contracts.SimpleToken.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.transfer_modelBody := by
  simpa using Contracts.SimpleToken.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.balanceOf_modelBody := by
  simpa using Contracts.SimpleToken.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.totalSupply_modelBody := by
  simpa using Contracts.SimpleToken.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.owner_modelBody := by
  simpa using Contracts.SimpleToken.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.mint_modelBody := by
  simpa using Contracts.ERC20.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.transfer_modelBody := by
  simpa using Contracts.ERC20.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.approve_modelBody := by
  simpa using Contracts.ERC20.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.transferFrom_modelBody := by
  simpa using Contracts.ERC20.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.balanceOf_modelBody := by
  simpa using Contracts.ERC20.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.allowanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.allowanceOf_modelBody := by
  simpa using Contracts.ERC20.allowanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.totalSupply_modelBody := by
  simpa using Contracts.ERC20.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.owner_modelBody := by
  simpa using Contracts.ERC20.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (GenericECMReadSmoke.snapshotQuote_model : Compiler.CompilationModel.FunctionSpec)) =
    GenericECMReadSmoke.snapshotQuote_modelBody := by
  simpa using GenericECMReadSmoke.snapshotQuote_semantic_preservation

example :
    GenericECMReadSmoke.snapshotQuote_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          ((fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)
            "quote")
          [ Compiler.CompilationModel.Expr.param "oracle"
          , Compiler.CompilationModel.Expr.param "asset"
          ]
      , Compiler.CompilationModel.Stmt.setStorage
          "lastQuote"
          (Compiler.CompilationModel.Expr.localVar "quote")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "quote")
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (GenericECMWriteSmoke.runEffect_model : Compiler.CompilationModel.FunctionSpec)) =
    GenericECMWriteSmoke.runEffect_modelBody := by
  simpa using GenericECMWriteSmoke.runEffect_semantic_preservation

example :
    GenericECMWriteSmoke.runEffect_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          genericECMEffectDemoModule
          [ Compiler.CompilationModel.Expr.param "lhs"
          , Compiler.CompilationModel.Expr.param "rhs"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (LowLevelTryCatchSmoke.catchFailure.run Verity.defaultState).getValue? = some 7 := by
  decide

example :
    (LowLevelTryCatchSmoke.skipCatchOnSuccess.run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    ((LowLevelTryCatchSmoke.catchFailureWithShadowedParam 5).run Verity.defaultState).getValue? = some 11 := by
  decide

example :
    LowLevelTryCatchSmoke.catchFailure_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "verity_try_success"
          (Compiler.CompilationModel.Expr.call
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0))
      , Compiler.CompilationModel.Stmt.ite
          (Compiler.CompilationModel.Expr.eq
            (Compiler.CompilationModel.Expr.localVar "verity_try_success")
            (Compiler.CompilationModel.Expr.literal 0))
          [ Compiler.CompilationModel.Stmt.setStorage
              "lastOutcome"
              (Compiler.CompilationModel.Expr.literal 7)
          ]
          []
      , Compiler.CompilationModel.Stmt.letVar
          "current"
          (Compiler.CompilationModel.Expr.storage "lastOutcome")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "current")
      ] := rfl

example :
    LowLevelTryCatchSmoke.catchFailureWithShadowedParam_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "verity_try_success_1"
          (Compiler.CompilationModel.Expr.call
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0))
      , Compiler.CompilationModel.Stmt.ite
          (Compiler.CompilationModel.Expr.eq
            (Compiler.CompilationModel.Expr.localVar "verity_try_success_1")
            (Compiler.CompilationModel.Expr.literal 0))
          [ Compiler.CompilationModel.Stmt.setStorage
              "lastOutcome"
              (Compiler.CompilationModel.Expr.literal 11)
          ]
          []
      , Compiler.CompilationModel.Stmt.letVar
          "current"
          (Compiler.CompilationModel.Expr.storage "lastOutcome")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "current")
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.mint_modelBody := by
  simpa using Contracts.ERC721.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.transferFrom_modelBody := by
  simpa using Contracts.ERC721.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.ownerOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.ownerOf_modelBody := by
  simpa using Contracts.ERC721.ownerOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.approve_modelBody := by
  simpa using Contracts.ERC721.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.getApproved_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.getApproved_modelBody := by
  simpa using Contracts.ERC721.getApproved_semantic_preservation


end Contracts.Smoke
