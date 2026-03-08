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

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract UintMapSmoke where
  storage
    values : Uint256 → Uint256 := slot 0

  function setValue (key : Uint256, value : Uint256) : Unit := do
    setMappingUint values key value

  function getValue (key : Uint256) : Uint256 := do
    let current ← getMappingUint values key
    return current

verity_contract Bytes32Smoke where
  storage
    value : Uint256 := slot 0

  function setDigest (digest : Bytes32) : Unit := do
    setStorage value digest

  function getDigest () : Bytes32 := do
    let digest ← getStorage value
    return digest

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

verity_contract CustomErrorSmoke where
  storage
    sentinel : Uint256 := slot 0

  errors
    error NonPositive(Uint256)
    error AmountTooLarge(Uint256, Uint256)

  function echo (amount : Uint256) : Uint256 := do
    return amount

verity_contract StatelessSmoke where
  storage

  function echoWord (value : Uint256) : Uint256 := do
    return value

  function whoAmI () : Address := do
    let sender ← msgSender
    return sender

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
end InitializerGuardFieldTypeRejected

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
end ConstantRuntimeBuiltinRejected

/--
error: contract immutables currently support only Uint256, Uint8, Address, Bytes32, and Bool; 'metadata' uses unsupported type
-/
#guard_msgs in
verity_contract ImmutableTypeRejected where
  storage

  immutables
    metadata : String := "paused"

  function metadataWord () : Uint256 := do
    return 0
end ImmutableTypeRejected

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
end ImmutableStorageNameConflictRejected

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
end ImmutableConstantNameConflictRejected

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
end DuplicateImmutableRejected

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

/--
error: linked external 'describe' uses unsupported parameter type; executable externalCall currently supports only Uint256, Uint8, Address, Bytes32, and Bool
-/
#guard_msgs in
verity_contract ExternalCallUnsupportedType where
  storage
  linked_externals
    external describe(String) -> (Uint256)

  function noop () : Unit := do
    pure ()
end ExternalCallUnsupportedType

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
end ExternalCallUnsupportedMultiReturn

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
end StructMappingWrongReadAccessor

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
end StructMappingWrongLegacyReadAccessor

/--
error: field 'positions' is not a nested struct mapping
-/
#guard_msgs in
verity_contract StructMappingWrongWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setStructMember2 "positions" owner owner "delegate" delegate_
end StructMappingWrongWriteAccessor

/--
error: field 'positions' is a struct-valued mapping; use setStructMember
-/
#guard_msgs in
verity_contract StructMappingWrongLegacyWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setMapping2 positions owner owner delegate_
end StructMappingWrongLegacyWriteAccessor

/--
error: unknown struct member 'nonce' on field 'positions'
-/
#guard_msgs in
verity_contract StructMappingUnknownMember where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setNonce (owner : Address, value : Uint256) : Unit := do
    setStructMember "positions" owner "nonce" value
end StructMappingUnknownMember

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
end StructMappingWrongScalarReadAccessor

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
end StructMappingWrongScalarAddressReadAccessor

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
#check_contract StatelessSmoke
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
