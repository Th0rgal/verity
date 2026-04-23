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

verity_contract StorageAddressArraySmoke where
  storage
    owners : Array Address := slot 0

  function size () : Uint256 := do
    let size ← getStorageArrayLength owners
    return size

  function firstOwner () : Address := do
    let owner ← getStorageArrayElement owners 0
    return owner

  function pushOwner (owner : Address) : Unit := do
    pushStorageArray owners owner

  function replaceFirstOwner (owner : Address) : Unit := do
    setStorageArrayElement owners 0 owner

verity_contract StorageBytes32ArraySmoke where
  storage
    digests : Array Bytes32 := slot 0

  function firstDigest () : Bytes32 := do
    let digest ← getStorageArrayElement digests 0
    return digest

  function pushDigest (digest : Bytes32) : Unit := do
    pushStorageArray digests digest

verity_contract StorageBoolArraySmoke where
  storage
    flags : Array Bool := slot 0

  function firstFlag () : Bool := do
    let flag ← getStorageArrayElement flags 0
    return flag

  function pushFlag (flag : Bool) : Unit := do
    pushStorageArray flags flag

  function setFirstFlag (flag : Bool) : Unit := do
    setStorageArrayElement flags 0 flag

def storageAddressArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageAddressArraySmoke.owners.slot then [11, 17] else [] }
  match StorageAddressArraySmoke.firstOwner seededState with
  | .success owner state =>
      owner == (11 : Address) &&
        state.storageArray StorageAddressArraySmoke.owners.slot == [11, 17]
  | .revert _ _ => false

example : storageAddressArrayExecutableReadsHead = true := by decide

def storageAddressArrayExecutablePushStoresWord : Bool :=
  match StorageAddressArraySmoke.pushOwner (19 : Address) Verity.defaultState with
  | .success () state =>
      state.storageArray StorageAddressArraySmoke.owners.slot == [19]
  | .revert _ _ => false

example : storageAddressArrayExecutablePushStoresWord = true := by decide

def storageAddressArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageAddressArraySmoke.owners.slot then [11, 17] else [] }
  match StorageAddressArraySmoke.replaceFirstOwner (29 : Address) seededState with
  | .success () state =>
      state.storageArray StorageAddressArraySmoke.owners.slot == [29, 17]
  | .revert _ _ => false

example : storageAddressArrayExecutableSetUpdatesHead = true := by decide

def storageBytes32ArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBytes32ArraySmoke.digests.slot then [41, 43] else [] }
  match StorageBytes32ArraySmoke.firstDigest seededState with
  | .success digest state =>
      digest == 41 &&
        state.storageArray StorageBytes32ArraySmoke.digests.slot == [41, 43]
  | .revert _ _ => false

example : storageBytes32ArrayExecutableReadsHead = true := by decide

def storageBoolArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBoolArraySmoke.flags.slot then [0, 1] else [] }
  match StorageBoolArraySmoke.firstFlag seededState with
  | .success flag state =>
      flag = false &&
        state.storageArray StorageBoolArraySmoke.flags.slot == [0, 1]
  | .revert _ _ => false

example : storageBoolArrayExecutableReadsHead = true := by decide

def storageBoolArrayExecutablePushStoresCanonicalWord : Bool :=
  match StorageBoolArraySmoke.pushFlag true Verity.defaultState with
  | .success () state =>
      state.storageArray StorageBoolArraySmoke.flags.slot == [1]
  | .revert _ _ => false

example : storageBoolArrayExecutablePushStoresCanonicalWord = true := by decide

def storageBoolArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBoolArraySmoke.flags.slot then [0, 1] else [] }
  match StorageBoolArraySmoke.setFirstFlag true seededState with
  | .success () state =>
      state.storageArray StorageBoolArraySmoke.flags.slot == [1, 1]
  | .revert _ _ => false

example : storageBoolArrayExecutableSetUpdatesHead = true := by decide

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

verity_contract StorageWordsAddressSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Address) : Array Uint256 := do
    returnStorageWords slots

verity_contract StorageWordsBoolSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bool) : Array Uint256 := do
    returnStorageWords slots

/--
error: returnStorageWords requires an array with single-word static elements on the compilation-model path, got Verity.Macro.ValueType.array (Verity.Macro.ValueType.bytes)
-/
#guard_msgs in
verity_contract StorageWordsUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bytes) : Array Uint256 := do
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

  function bitAndSignBit (lhs : Int256, rhs : Int256) : Bool := do
    return (bitAnd lhs rhs < 0)

  function minSignBit (lhs : Int256) : Bool := do
    return (min lhs 0 < 0)

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
error: duplicate function declaration 'echo()'
-/
#guard_msgs in
verity_contract DuplicateFunctionRejected where
  storage

  function echo () : Uint256 := do
    return 1

  function echo () : Uint256 := do
    return 2

verity_contract FunctionOverloadSmoke where
  storage

  function echo (a : Uint256) : Uint256 := do
    return a

  function echo (a : Address) : Uint256 := do
    return (addressToWord a)

  function echo (a : Uint256, b : Uint256) : Uint256 := do
    return (add a b)

/--
error: duplicate function ABI signature 'echo(scalar_uint256)' after newtype erasure
-/
#guard_msgs in
verity_contract NewtypeErasedOverloadRejected where
  types
    Amount : Uint256
    Shares : Uint256
  storage

  function echo (a : Amount) : Uint256 := do
    return a

  function echo (a : Shares) : Uint256 := do
    return a

verity_contract HelperExternalArgumentSmoke where
  storage
    saved : Uint256 := slot 0

  linked_externals
    external echo(Uint256) -> (Uint256)

  function idWord (a : Uint256) : Uint256 := do
    return a

  function pair (a : Uint256) : Tuple [Uint256, Uint256] := do
    return (a, add a 1)

  function put (a : Uint256) : Unit := do
    setStorage saved a

  function bindExternalArg (x : Uint256) : Uint256 := do
    let y ← idWord (externalCall "echo" [x])
    return y

  function tupleExternalArg (x : Uint256) : Uint256 := do
    let (a, b) ← pair (externalCall "echo" [x])
    return (add a b)

  function statementExternalArg (x : Uint256) : Unit := do
    put (externalCall "echo" [x])

verity_contract BlockTimestampSmoke where
  storage

  function nowish () : Uint256 := do
    let t ← Verity.blockTimestamp
    return t

  function timestampPlus (delta : Uint256) : Uint256 := do
    let t ← blockTimestamp
    return (add t delta)

  function blobFeePlus (delta : Uint256) : Uint256 := do
    let fee ← blobbasefee
    return (add fee delta)

example :
    (BlockTimestampSmoke.nowish.run { Verity.defaultState with blockTimestamp := 123 }).getValue? =
      some 123 := by
  decide

example :
    (BlockTimestampSmoke.timestampPlus 7 |>.run { Verity.defaultState with blockTimestamp := 123 }).getValue? =
      some 130 := by
  decide

example :
    (BlockTimestampSmoke.blobFeePlus 7 |>.run { Verity.defaultState with blobBaseFee := 123 }).getValue? =
      some 130 := by
  decide

/--
error: context accessor 'blockTimestamp' is monadic; use `let x ← blockTimestamp` before using it in a pure expression
-/
#guard_msgs in
verity_contract PureBlockTimestampAccessorRejected where
  storage

  function nowish () : Uint256 := do
    let t := blockTimestamp
    return t

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

/--
error: function 'structMember' conflicts with reserved generated declaration 'structMember'
-/
#guard_msgs in
verity_contract StructMappingGeneratedReadHelperCollisionRejected where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function structMember () : Uint256 := do
    return 1

/--
error: immutable 'setStructMember2' conflicts with reserved generated declaration 'setStructMember2'
-/
#guard_msgs in
verity_contract StructMappingGeneratedWriteHelperImmutableCollisionRejected where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  immutables
    setStructMember2 : Uint256 := 1

  constructor () := do
    pure ()

  function allowanceOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember2 "approvals" owner spender "allowance"
    return amount

/--
error: function 'quote' generates internal declaration 'quote__scalar_uint256' that conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ConstantOverloadGeneratedNameCollisionRejected where
  storage

  constants
    quote__scalar_uint256 : Uint256 := 7

  function quote (amount : Uint256) : Uint256 := do
    return amount

  function quote (recipient : Address) : Uint256 := do
    return (addressToWord recipient)

/--
error: function 'quote' generates internal declaration 'quote__scalar_uint256' that conflicts with an immutable of the same name
-/
#guard_msgs in
verity_contract ImmutableOverloadGeneratedNameCollisionRejected where
  storage

  immutables
    quote__scalar_uint256 : Uint256 := 7

  function quote (amount : Uint256) : Uint256 := do
    return amount

  function quote (recipient : Address) : Uint256 := do
    return (addressToWord recipient)

#guard_msgs in
verity_contract OverloadSignatureEncodingSmoke where
  types
    tuple_uint256 : Uint256
  storage

  function quote (amount : tuple_uint256) : Uint256 := do
    return amount

  function quote (pair : Tuple [Uint256, Uint256]) : Uint256 := do
    let _pairValue := pair
    return pair_0

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

verity_contract CurveCutArraySmoke where
  storage
    lastXt : Uint256 := slot 0
    lastLiq : Uint256 := slot 1
    lastOffset : Uint256 := slot 2

  function firstCutXt (cuts : Array (Tuple [Uint256, Uint256, Int256])) : Uint256 := do
    let (xtReserve, _liqSquare, _offset) := arrayElement cuts 0
    return xtReserve

  function returnCut (cuts : Array (Tuple [Uint256, Uint256, Int256]), idx : Uint256) : Tuple [Uint256, Uint256, Int256] := do
    return arrayElement cuts idx

  function storeCut (cuts : Array (Tuple [Uint256, Uint256, Int256]), idx : Uint256) : Unit := do
    let (xtReserve, liqSquare, offset) := arrayElement cuts idx
    setStorage lastXt xtReserve
    setStorage lastLiq liqSquare
    setStorage lastOffset (toUint256 offset)

  function storeTwoCuts (cuts : Array (Tuple [Uint256, Uint256, Int256]), firstIdx : Uint256, secondIdx : Uint256) : Unit := do
    let (firstXt, _firstLiq, _firstOffset) := arrayElement cuts firstIdx
    let (secondXt, _secondLiq, _secondOffset) := arrayElement cuts secondIdx
    setStorage lastXt firstXt
    setStorage lastLiq secondXt

/--
error: arrayElement currently supports only arrays with single-word static elements on the compilation-model path, got Verity.Macro.ValueType.array
  (Verity.Macro.ValueType.tuple [Verity.Macro.ValueType.uint256, Verity.Macro.ValueType.uint256])
-/
#guard_msgs in
verity_contract CurveCutPlainTupleArrayElementRejected where
  storage

  function badPlainRead (cuts : Array (Tuple [Uint256, Uint256])) : Uint256 := do
    let cut := arrayElement cuts 0
    return 0

def curveCutArrayExecutableReadsTupleElement : Bool :=
  match CurveCutArraySmoke.firstCutXt #[(11, 13, toInt256 17)] Verity.defaultState with
  | .success value _ => value == 11
  | _ => false

example : curveCutArrayExecutableReadsTupleElement = true := by decide

verity_contract PackedStorageWriteSmoke where
  storage
    stateRoot : Uint256 := slot 0

  function writeSlot0 (isClosed : Bool, maxTotalSupply : Uint256) : Unit := do
    let closedWord := boolToWord isClosed
    let slot0 := bitOr closedWord (shl 8 maxTotalSupply)
    setPackedStorage stateRoot 0 slot0

  function writeSlot1 (accruedProtocolFees : Uint256, normalizedUnclaimedWithdrawals : Uint256) : Unit := do
    let slot1 := bitOr accruedProtocolFees (shl 128 normalizedUnclaimedWithdrawals)
    setPackedStorage stateRoot 1 slot1

def packedStorageExecutableWritesExplicitWordOffset : Bool :=
  match PackedStorageWriteSmoke.writeSlot1 7 9 Verity.defaultState with
  | .success _ state =>
      state.storage 0 == 0 &&
      state.storage 1 == bitOr 7 (shl 128 9)
  | _ => false

example : packedStorageExecutableWritesExplicitWordOffset = true := by decide

verity_contract DirectHelperCallSmoke where
  storage
    total : Uint256 := slot 0
    lastLeft : Uint256 := slot 1
    lastRight : Uint256 := slot 2

  function addToTotal (amount : Uint256) : Unit := do
    let current ← getStorage total
    setStorage total (add current amount)

  function readTotalPlus (extra : Uint256) : Uint256 := do
    let current ← getStorage total
    return (add current extra)

  function pairWithTotal (offset : Uint256) : Tuple [Uint256, Uint256] := do
    let current ← getStorage total
    return (current, add current offset)

  function allow_post_interaction_writes runHelpers (amount : Uint256, extra : Uint256, offset : Uint256) : Uint256 := do
    addToTotal amount
    let combined ← readTotalPlus extra
    let (left, right) ← pairWithTotal offset
    setStorage lastLeft left
    setStorage lastRight right
    return combined

  function snapshot () : Tuple [Uint256, Uint256, Uint256] := do
    let current ← getStorage total
    let left ← getStorage lastLeft
    let right ← getStorage lastRight
    return (current, left, right)

/--
error: helper call 'consumePayload' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs
-/
#guard_msgs in
verity_contract DirectHelperCallDynamicEffectRejected where
  storage

  function consumePayload (_payload : Bytes) : Unit := do
    pure ()

  function run (payload : Bytes) : Unit := do
    consumePayload payload

/--
error: helper call 'measurePayload' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs
-/
#guard_msgs in
verity_contract DirectHelperCallDynamicBindRejected where
  storage

  function measurePayload (_payload : Bytes) : Uint256 := do
    return 0

  function run (payload : Bytes) : Uint256 := do
    let measured ← measurePayload payload
    return measured

/--
error: helper call 'fanoutPayload' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs
-/
#guard_msgs in
verity_contract DirectHelperCallDynamicTupleRejected where
  storage

  function fanoutPayload (_payload : Bytes) : Tuple [Uint256, Uint256] := do
    return (0, 1)

  function run (payload : Bytes) : Tuple [Uint256, Uint256] := do
    let (left, right) ← fanoutPayload payload
    return (left, right)

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

verity_contract ContextAccessorShadowSmoke where
  storage

  constants
    chainid : Uint256 := 31337

  immutables
    blockTimestamp : Uint256 := 12345
    msgSender : Address := (wordToAddress 42)

  function echoSenderName (msgSender : Address) : Address := do
    return msgSender

  function constantNamedChainid () : Uint256 := do
    return chainid

  function immutableNamedBlockTimestamp () : Uint256 := do
    return blockTimestamp

  function immutableNamedMsgSender () : Address := do
    return msgSender

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

private def _structMemberExecutableHelper :
    String → Address → String → Contract Uint256 :=
  StructMappingSmoke.structMember
private def _setStructMemberExecutableHelper :
    String → Address → String → Uint256 → Contract Unit :=
  StructMappingSmoke.setStructMember
private def _structMember2ExecutableHelper :
    String → Address → Address → String → Contract Uint256 :=
  StructMappingSmoke.structMember2
private def _setStructMember2ExecutableHelper :
    String → Address → Address → String → Uint256 → Contract Unit :=
  StructMappingSmoke.setStructMember2

verity_contract ExternalCallSmoke where
  storage
    echoedValue : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)
    external echo_try(Uint256) -> (Bool, Uint256)

  function allow_post_interaction_writes storeEcho (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage echoedValue echoed

  function getEchoedValue () : Uint256 := do
    let current ← getStorage echoedValue
    return current

-- tryExternalCall smoke: single-return external with success flag (#1727, Axis 1 Step 5f)
verity_contract TryExternalCallSmoke where
  storage
    lastResult : Uint256 := slot 0
    callSucceeded : Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)
    external echo_try(Uint256) -> (Bool, Uint256)

  function allow_post_interaction_writes tryEcho (x : Uint256) : Unit := do
    let (success, result) ← tryExternalCall "echo" [x]
    if success then
      setStorage lastResult result
      setStorage callSucceeded 1
    else
      setStorage callSucceeded 0

verity_contract ERC20HelperSmoke where
  storage
    lastBalance : Uint256 := slot 0
    lastAllowance : Uint256 := slot 1
    lastSupply : Uint256 := slot 2

  function pushTokens (token : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransfer token toAddr amount

  function pullTokens (token : Address, fromAddr : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransferFrom token fromAddr toAddr amount

  function approveTokens (token : Address, spender : Address, amount : Uint256) : Unit := do
    safeApprove token spender amount

  function allow_post_interaction_writes snapshotBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    setStorage lastBalance balance
    return balance

  function allow_post_interaction_writes snapshotAllowance (token : Address, owner : Address, spender : Address) : Uint256 := do
    let current ← allowance token owner spender
    setStorage lastAllowance current
    return current

  function allow_post_interaction_writes snapshotSupply (token : Address) : Uint256 := do
    let supply ← totalSupply token
    setStorage lastSupply supply
    return supply

verity_contract GenericECMReadSmoke where
  storage
    lastQuote : Uint256 := slot 0

  function allow_post_interaction_writes snapshotQuote (oracle : Address, asset : Address) : Uint256 := do
    let quote ← ecmCall
      (fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)
      [oracle, asset]
    setStorage lastQuote quote
    return quote

verity_contract GenericECMWriteSmoke where
  storage

  function runEffect (lhs : Uint256, rhs : Uint256) : Unit := do
    ecmDo genericECMEffectDemoModule [lhs, rhs]

set_option linter.unusedVariables false in
verity_contract LowLevelTryCatchSmoke where
  storage
    lastOutcome : Uint256 := slot 0

  function allow_post_interaction_writes catchFailure ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 1 0 0 0 0) (do
      setStorage lastOutcome 7)
    let current ← getStorage lastOutcome
    return current

  function allow_post_interaction_writes skipCatchOnSuccess ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 1 0 0 0 0 0 0) (do
      setStorage lastOutcome 9)
    let current ← getStorage lastOutcome
    return current

  function allow_post_interaction_writes catchFailureWithShadowedParam (verity_try_success : Uint256)
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 1 0 0 0 0) (do
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

  function writeShadowedTransfer (token : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransfer token toAddr amount

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

-- Multi-return externals are now allowed (Step 5f); use tryExternalCall
-- to call them with a success flag.
verity_contract ExternalCallMultiReturn where
  storage
    lastValue : Uint256 := slot 0
  linked_externals
    external fanout(Uint256) -> (Uint256, Address)
    external fanout_try(Uint256) -> (Bool, Uint256, Address)

  function allow_post_interaction_writes callFanout (x : Uint256) : Unit := do
    let (success, value, addr) ← tryExternalCall "fanout" [x]
    if success then
      setStorage lastValue value
      setStorage lastValue addr
    else
      pure ()

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
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeFunctionBoundary': Compilation error: function 'preview' uses low-level/assembly mechanic(s) calldataload outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
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
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeConstructorBoundary': Compilation error: constructor uses low-level/assembly mechanic(s) mstore outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
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
#check_contract StorageAddressArraySmoke
#check_contract StorageBoolArraySmoke
#check_contract StorageBytes32ArraySmoke
#check_contract MappingWordSmoke
#check_contract StorageWordsSmoke
#check_contract CustomErrorSmoke
#check_contract SignedBuiltinSmoke
#check_contract StatelessSmoke
#check_contract SpecialEntrypointSmoke
#check_contract TupleSmoke
#check_contract CurveCutArraySmoke
#check_contract PackedStorageWriteSmoke
#check_contract DirectHelperCallSmoke
#check_contract Uint8Smoke
#check_contract AddressHelpersSmoke
#check_contract ZeroAddressShadowSmoke
#check_contract ContextAccessorShadowSmoke
#check_contract FunctionOverloadSmoke
#check_contract HelperExternalArgumentSmoke
#check_contract BlockTimestampSmoke
#check_contract StructMappingSmoke
#check_contract ExternalCallSmoke
#check_contract TryExternalCallSmoke
#check_contract ExternalCallMultiReturn
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
    (LowLevelTryCatchSmoke.catchFailure.run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    (LowLevelTryCatchSmoke.skipCatchOnSuccess.run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    ((LowLevelTryCatchSmoke.catchFailureWithShadowedParam 5).run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    LowLevelTryCatchSmoke.catchFailure_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "verity_try_success"
          (Compiler.CompilationModel.Expr.call
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 1)
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
            (Compiler.CompilationModel.Expr.literal 1)
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


-- #1729, Axis 3 Step 1b: smoke test for modifies(...) annotation
verity_contract ModifiesSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1
    balances : Address → Uint256 := slot 2

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  -- Only modifies `counter`; owner and balances are untouched
  function increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Modifies `owner` only
  function transferOwnership (newOwner : Address) modifies(owner) : Unit := do
    setStorageAddr owner newOwner

  -- Modifies both counter and balances
  function deposit (amount : Uint256) modifies(counter, balances) : Unit := do
    let sender ← msgSender
    let current ← getStorage counter
    setStorage counter (add current 1)
    let balance ← getMapping balances sender
    setMapping balances sender (add balance amount)

  -- View function (no modifies needed)
  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

-- #1729, Axis 3 Step 1c: smoke test for no_external_calls annotation
verity_contract NoExternalCallsSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1

  -- Pure arithmetic, no external calls
  function no_external_calls increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Read-only with no_external_calls
  function view no_external_calls getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- Regular function without the annotation (for comparison)
  function setOwner (newOwner : Address) : Unit := do
    setStorageAddr owner newOwner

-- #1729, Axis 3 Step 1d: smoke test for annotation composition (_effects theorem)
verity_contract EffectCompositionSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1
    balances : Address → Uint256 := slot 2

  -- view + no_external_calls: _effects bundles _is_view ∧ _no_calls
  function view no_external_calls getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- no_external_calls + modifies: _effects bundles _no_calls ∧ _modifies
  function no_external_calls increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Single annotation only (no _effects expected)
  function no_external_calls setOwner (newOwner : Address) : Unit := do
    setStorageAddr owner newOwner

  -- No annotations at all
  function deposit (amount : Uint256) : Unit := do
    let sender ← msgSender
    let balance ← getMapping balances sender
    setMapping balances sender (add balance amount)

-- #1728, Axis 2 Step 2a: smoke test for CEI enforcement
verity_contract CEISmoke where
  storage
    counter : Uint256 := slot 0
    balances : Address → Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- CEI-compliant: effects before interactions (no external calls here)
  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- CEI-compliant: no state writes at all (view-like)
  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- CEI-compliant: effects before interaction
  function updateThenCall (next : Uint256) : Uint256 := do
    setStorage counter next
    let echoed := externalCall "echo" [next]
    return echoed

  -- Opted out with allow_post_interaction_writes: writes after call
  function allow_post_interaction_writes callThenUpdate (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage counter echoed

-- #1728, Axis 2 Step 2b: smoke test for CEI escalation ladder (nonreentrant, cei_safe)
verity_contract CEILadderSmoke where
  storage
    counter : Uint256 := slot 0
    lock : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- nonreentrant is recorded as metadata; it does not bypass CEI by itself.
  function nonreentrant(lock) callThenStoreGuarded (x : Uint256) : Uint256 := do
    setStorage counter x
    let echoed := externalCall "echo" [x]
    return echoed

  -- cei_safe is recorded as metadata; it does not bypass CEI by itself.
  function cei_safe callThenStoreProved (x : Uint256) : Uint256 := do
    setStorage counter x
    let echoed := externalCall "echo" [x]
    return echoed

  -- Normal function: CEI-compliant (effects before interactions), gets _cei_compliant
  function storeThenCall (x : Uint256) : Uint256 := do
    setStorage counter x
    let echoed := externalCall "echo" [x]
    return echoed

  -- Normal function: no external calls at all, gets _cei_compliant
  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

-- Roles / requires(field) smoke test (#1728, Axis 2 Step 2c)
verity_contract RolesSmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- requires(admin) auto-injects: require(caller == admin) "Access denied: caller is not admin"
  function setCounter (value : Uint256) requires(admin) : Unit := do
    setStorage counter value

  -- Normal function without access control
  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

-- Newtype smoke test (#1727, Axis 1 Step 3a)
-- Declares semantic newtypes that are erased to base types at EVM level
verity_contract NewtypeSmoke where
  types
    TokenId : Uint256
    Amount : Uint256
    Owner : Address
  storage
    nextTokenId : Uint256 := slot 0
    totalSupply : Uint256 := slot 1
    minter : Address := slot 2

  constructor (initialMinter : Address) := do
    setStorageAddr minter initialMinter

  -- Newtypes are erased to their base types: TokenId → Uint256, Amount → Uint256
  function mint (id : TokenId, amount : Amount) : Unit := do
    setStorage nextTokenId id
    let current ← getStorage totalSupply
    setStorage totalSupply (add current amount)

  -- Owner erases to Address
  function setMinter (newMinter : Owner) : Unit := do
    setStorageAddr minter newMinter

  function getNextTokenId () : Uint256 := do
    let current ← getStorage nextTokenId
    return current

#check_contract RolesSmoke
#check_contract NewtypeSmoke

-- Smoke test for newtype-TYPED storage fields (not just newtype params).
-- Verifies that setStorage/setStorageAddr/getStorage/getStorageAddr work
-- when the storage field itself is declared with a newtype type.
verity_contract NewtypeStorageSmoke where
  types
    TokenId : Uint256
    Owner : Address
  storage
    currentTokenId : TokenId := slot 0
    admin : Owner := slot 1

  constructor (initialAdmin : Owner) := do
    setStorageAddr admin initialAdmin

  function setTokenId (id : TokenId) : Unit := do
    setStorage currentTokenId id

  function getTokenId () : Uint256 := do
    let tid ← getStorage currentTokenId
    return tid

  function setAdmin (newAdmin : Owner) : Unit := do
    setStorageAddr admin newAdmin

  function getAdmin () : Address := do
    let a ← getStorageAddr admin
    return a

#check_contract NewtypeStorageSmoke

-- Every contract emits a storageNamespace : Nat definition (#1730, Axis 4 Step 4a).
-- Verify a few representative contracts have it and it is a Nat.
example : Contracts.Counter.storageNamespace = Contracts.Counter.storageNamespace := rfl
example : NewtypeSmoke.storageNamespace = NewtypeSmoke.storageNamespace := rfl

-- Namespaced storage smoke test (#1730, Axis 4 Step 4b).
-- When `storage_namespace` is present, user-declared slot numbers are offset
-- by keccak256("{ContractName}.storage.v0") so different contracts never collide.
verity_contract NamespacedStorageSmoke where
  storage_namespace
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function deposit (amount : Uint256) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function getOwner () : Address := do
    let addr ← getStorageAddr owner
    return addr

#check_contract NamespacedStorageSmoke

-- Verify that NamespacedStorageSmoke's storage slots differ from
-- non-namespaced contracts: slot 0 is offset by the namespace base.
-- The slot values embed the keccak-based namespace offset.
example : NamespacedStorageSmoke.balance.slot ≠ 0 := by decide
example : NamespacedStorageSmoke.owner.slot ≠ 1 := by decide

-- Verify storageNamespace flows into the CompilationModel spec (#1730, Axis 4 Step 4d).
-- Namespaced contracts carry `some ns`; non-namespaced carry `none`.
example : NamespacedStorageSmoke.spec.storageNamespace.isSome = true := rfl
example : Contracts.Counter.spec.storageNamespace.isNone = true := rfl

-- Custom namespace override (#1730, Axis 4 Step 4c)
-- Uses `storage_namespace "custom.v0"` instead of the default contract-name-based key.
-- The keccak256 is computed on the literal string "custom.v0".
verity_contract CustomNamespacedSmoke where
  storage_namespace "custom.v0"
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  function deposit (amount : Uint256) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function getOwner () : Address := do
    let addr ← getStorageAddr owner
    return addr

#check_contract CustomNamespacedSmoke

-- Verify custom namespace: slots are offset (nonzero) and differ from the
-- default-namespaced contract (which uses keccak256("NamespacedStorageSmoke.storage.v0")).
example : CustomNamespacedSmoke.balance.slot ≠ 0 := by decide
example : CustomNamespacedSmoke.owner.slot ≠ 1 := by decide
example : CustomNamespacedSmoke.balance.slot ≠ NamespacedStorageSmoke.balance.slot := by decide
example : CustomNamespacedSmoke.spec.storageNamespace.isSome = true := rfl
-- Verify the exported storageNamespace constant matches the spec value (not the default contract name hash).
example : CustomNamespacedSmoke.storageNamespace = CustomNamespacedSmoke.spec.storageNamespace.get! := rfl
example : CustomNamespacedSmoke.storageNamespace = 105542539407630759878214364786123406227647255732885741380220581264062975076298 := rfl
example : CustomNamespacedSmoke.storageNamespace ≠ 67387409610395734986217237394999073412260967828994783805404864304835768435504 := by decide

-- ADT (inductive) section smoke test (#1727, Axis 1 Steps 5a/5b)
-- Declares algebraic data types with typed variant fields.
-- ADT type definitions flow through to ContractSpec.adtTypes.
-- ADT-typed storage fields are represented as Uint256 (tag value) at the EVM level.
verity_contract AdtSmoke where
  types
    TokenId : Uint256
  inductive
    OptionalUint := | Some(value : Uint256) | None
    Result := | Ok(amount : Uint256, recipient : Address) | Err(code : Uint256)
  storage
    counter : Uint256 := slot 0
    result : OptionalUint := slot 1

  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

#check_contract AdtSmoke

-- Verify ADT type definitions flow through to spec (#1727, Step 5b plumbing)
example : AdtSmoke.spec.adtTypes.length = 2 := rfl
example : AdtSmoke.spec.adtTypes.map (·.name) = ["OptionalUint", "Result"] := rfl
example : (AdtSmoke.spec.adtTypes.map (·.variants.length)) = [2, 2] := rfl

-- Unsafe block smoke test (#1424, Phase 6 Step 6a).
-- `unsafe "reason" do` wraps a block of statements; Step 6a is the transparent
-- wrapper (validation/compilation recurse into the body unchanged).
verity_contract UnsafeBlockSmoke where
  storage
    counter : Uint256 := slot 0

  function incrementUnsafe () : Unit := do
    unsafe "demo: testing unsafe block syntax" do
      let current ← getStorage counter
      setStorage counter (add current 1)

  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract UnsafeBlockSmoke

-- Unsafe gating positive test (#1728, Phase 6 Step 6b).
-- Low-level mstore inside `unsafe` block passes #check_contract
-- WITHOUT requiring local_obligations.
verity_contract UnsafeGatingAccepted where
  storage
    counter : Uint256 := slot 0

  function writeMem () : Unit := do
    unsafe "manual memory write for packed encoding" do
      mstore 0 1
    pure ()

#check_contract UnsafeGatingAccepted

-- Unsafe gating negative test (#1728, Phase 6 Step 6b).
-- Low-level mstore OUTSIDE unsafe block (and no local_obligations) is rejected.
verity_contract UnsafeGatingRejected where
  storage

  constructor () := do
    mstore 0 1
    pure ()

  function noop () : Unit := do
    pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.UnsafeGatingRejected': Compilation error: constructor uses low-level/assembly mechanic(s) mstore outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract UnsafeGatingRejected

-- CEI violation test: this contract compiles but #check_contract rejects it
verity_contract CEIViolationRejected where
  storage
    result : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function callThenStore (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    setStorage result echoed

/--
error: #check_contract failed for 'Contracts.Smoke.CEIViolationRejected': Compilation error: function 'callThenStore' violates CEI (Checks-Effects-Interactions) ordering: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIViolationRejected

/--
error: function 'guarded': nonreentrant lock field 'lock' must be a scalar Uint256 storage field
-/
#guard_msgs in
verity_contract NonreentrantAddressLockRejected where
  storage
    lock : Address := slot 0

  function nonreentrant(lock) guarded () : Unit := do
    pure ()

-- ════════════════════════════════════════════════════════════════════════════
-- Stress-test contracts: edge-case coverage for Language Design Axes (#1731)
-- ════════════════════════════════════════════════════════════════════════════

-- CEI edge case 1: write after external call, inside an if-branch — should detect
verity_contract CEIWriteInBranchAfterCall where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- Call then conditional write: CEI violation
  function callThenConditionalWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    if echoed != 0 then
      setStorage counter echoed
    else
      pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.CEIWriteInBranchAfterCall': Compilation error: function 'callThenConditionalWrite' violates CEI (Checks-Effects-Interactions) ordering: in if-then branch: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIWriteInBranchAfterCall

-- CEI edge case 2: call at top level, write after — same as CEIViolationRejected but
-- with the write in both branches of an if (to test compound-statement propagation)
verity_contract CEICallBothBranchesWrite where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function callThenBranchWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    if echoed != 0 then
      setStorage counter echoed
    else
      setStorage counter 0

/--
error: #check_contract failed for 'Contracts.Smoke.CEICallBothBranchesWrite': Compilation error: function 'callThenBranchWrite' violates CEI (Checks-Effects-Interactions) ordering: in if-then branch: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEICallBothBranchesWrite

-- Modifies + roles: combined annotation
verity_contract ModifiesRolesSmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1
    flag : Uint256 := slot 2

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- Combines requires(admin), modifies(counter), and no_external_calls
  function no_external_calls setCounter (value : Uint256) requires(admin) modifies(counter) : Unit := do
    setStorage counter value

  -- Combines requires(admin) and modifies(counter, flag)
  function setCounterAndFlag (value : Uint256, flagValue : Uint256) requires(admin) modifies(counter, flag) : Unit := do
    setStorage counter value
    setStorage flag flagValue

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract ModifiesRolesSmoke

-- Modifies + namespace: namespaced storage with modifies annotations
verity_contract ModifiesNamespaceSmoke where
  storage_namespace
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  function transferOwnership (newOwner : Address) modifies(owner) : Unit := do
    setStorageAddr owner newOwner

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract ModifiesNamespaceSmoke

-- Verify namespaced modifies slots are actually offset
example : ModifiesNamespaceSmoke.counter.slot ≠ 0 := by decide
example : ModifiesNamespaceSmoke.owner.slot ≠ 1 := by decide

-- ADT edge case: single variant (no branching needed)
verity_contract AdtSingleVariant where
  inductive
    Sentinel := | Active
  storage
    tag : Sentinel := slot 0

  function store () : Unit := do
    setStorage tag (adt "Active")

#check_contract AdtSingleVariant

-- ADT edge case: variant with zero fields vs variant with multiple fields
verity_contract AdtMixedFieldCounts where
  inductive
    Maybe := | Nothing | Just(value : Uint256)
    Pair := | MkPair(fst : Uint256, snd : Uint256)
  storage
    result : Maybe := slot 0

  function clear () : Unit := do
    setStorage result (adt "Nothing")

  function set (_value : Uint256) : Unit := do
    setStorage result (adt "Just" [_value])

#check_contract AdtMixedFieldCounts

-- Verify ADT spec plumbing for mixed field counts
example : AdtMixedFieldCounts.spec.adtTypes.length = 2 := rfl
example : AdtMixedFieldCounts.spec.adtTypes.map (·.name) = ["Maybe", "Pair"] := rfl

-- Newtype + modifies: newtypes used in function params with modifies annotation
verity_contract NewtypeModifiesSmoke where
  types
    TokenId : Uint256
    Amount : Uint256
  storage
    nextTokenId : Uint256 := slot 0
    totalMinted : Uint256 := slot 1

  function mint (id : TokenId, amount : Amount) modifies(nextTokenId, totalMinted) : Unit := do
    setStorage nextTokenId id
    let current ← getStorage totalMinted
    setStorage totalMinted (add current amount)

  function view getNextId () : Uint256 := do
    let current ← getStorage nextTokenId
    return current

#check_contract NewtypeModifiesSmoke

-- Newtype + namespace combo
verity_contract NewtypeNamespaceSmoke where
  types
    TokenId : Uint256
  storage_namespace "newtype.ns.v0"
  storage
    nextId : Uint256 := slot 0

  function setId (id : TokenId) : Unit := do
    setStorage nextId id

  function view getId () : Uint256 := do
    let current ← getStorage nextId
    return current

#check_contract NewtypeNamespaceSmoke

-- Verify namespace offset applies
example : NewtypeNamespaceSmoke.nextId.slot ≠ 0 := by decide

-- Unsafe block + CEI: write after unsafe block that has a call — should detect
verity_contract UnsafeCEIViolation where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function unsafeCallThenWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    unsafe "test: write inside unsafe after call" do
      setStorage counter echoed

/--
error: #check_contract failed for 'Contracts.Smoke.UnsafeCEIViolation': Compilation error: function 'unsafeCallThenWrite' violates CEI (Checks-Effects-Interactions) ordering: in unsafe block: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract UnsafeCEIViolation

-- Unsafe block + CEI: write inside unsafe before call — should pass
verity_contract UnsafeCEICompliant where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function writeBeforeUnsafeCall (x : Uint256) : Uint256 := do
    setStorage counter x
    unsafe "test: call inside unsafe after write" do
      let echoed := externalCall "echo" [x]
      return echoed

#check_contract UnsafeCEICompliant

-- CEI: internal call after external call — the internal call may write storage,
-- so this should be flagged as a CEI violation.
verity_contract CEIInternalCallAfterExternalRejected where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function increment (amount : Uint256) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current amount)

  function callThenHelper (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    increment echoed

/--
error: #check_contract failed for 'Contracts.Smoke.CEIInternalCallAfterExternalRejected': Compilation error: function 'callThenHelper' violates CEI (Checks-Effects-Interactions) ordering: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIInternalCallAfterExternalRejected

-- Roles + CEI combo: role guard with CEI-compliant external call
verity_contract RolesCEISmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- CEI compliant: write, then call
  function setAndCall (value : Uint256) requires(admin) : Uint256 := do
    setStorage counter value
    let echoed := externalCall "echo" [value]
    return echoed

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract RolesCEISmoke

-- Nonreentrant + modifies: combined annotations
verity_contract NonreentrantModifiesSmoke where
  storage
    lock : Uint256 := slot 0
    counter : Uint256 := slot 1
    balance : Uint256 := slot 2
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- nonreentrant metadata composes with modifies, while the body remains CEI-ordered.
  function nonreentrant(lock) deposit (amount : Uint256) modifies(counter, balance) : Uint256 := do
    let current ← getStorage counter
    setStorage counter (add current 1)
    let bal ← getStorage balance
    setStorage balance (add bal amount)
    let echoed := externalCall "echo" [amount]
    return echoed

  function view getBalance () : Uint256 := do
    let bal ← getStorage balance
    return bal

#check_contract NonreentrantModifiesSmoke

-- Multiple ADTs + newtype in same contract
verity_contract AdtNewtypeCombo where
  types
    TokenId : Uint256
    Owner : Address
  inductive
    Status := | Active | Paused | Deprecated
    OptionalId := | SomeId(id : Uint256) | NoId
  storage
    contractStatus : Status := slot 0
    lastTokenId : OptionalId := slot 1

  function pause () : Unit := do
    setStorage contractStatus (adt "Paused")

  function unpause () : Unit := do
    setStorage contractStatus (adt "Active")

  function setLastId (_id : TokenId) : Unit := do
    setStorage lastTokenId (adt "SomeId" [_id])

#check_contract AdtNewtypeCombo

-- Verify ADT spec for 3-variant enum
example : AdtNewtypeCombo.spec.adtTypes.length = 2 := rfl
example : AdtNewtypeCombo.spec.adtTypes.map (·.name) = ["Status", "OptionalId"] := rfl
-- Status has 3 variants: Active(0), Paused(1), Deprecated(2); OptionalId has 2
example : AdtNewtypeCombo.spec.adtTypes.map (·.variants.length) = [3, 2] := rfl

-- Full combo: namespace + newtype + modifies + roles + CEI
verity_contract FullComboSmoke where
  types
    Amount : Uint256
  inductive
    TokenStatus := | Active | Frozen
  storage_namespace "fullcombo.v0"
  storage
    admin : Address := slot 0
    balance : Uint256 := slot 1
    status : TokenStatus := slot 2

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  function no_external_calls deposit (amount : Amount) requires(admin) modifies(balance) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function no_external_calls freeze () requires(admin) modifies(status) : Unit := do
    setStorage status (adt "Frozen")

  function view no_external_calls getBalance () : Uint256 := do
    let current ← getStorage balance
    return current

#check_contract FullComboSmoke

-- Verify combo properties
example : FullComboSmoke.balance.slot ≠ 1 := by decide  -- namespaced
example : FullComboSmoke.spec.storageNamespace.isSome = true := rfl
example : FullComboSmoke.spec.adtTypes.length = 1 := rfl
example : FullComboSmoke.spec.adtTypes.map (·.name) = ["TokenStatus"] := rfl

end Contracts.Smoke
