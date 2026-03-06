import Verity.Specs.Common

namespace Verity.Macro

set_option hygiene false

syntax (name := genSpecCmd)
  "#gen_spec " ident " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdExtra)
  "#gen_spec " ident " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecCmdFor)
  "#gen_spec " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdForExtra)
  "#gen_spec " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmd)
  "#gen_spec_addr " ident " (" term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdExtra)
  "#gen_spec_addr " ident " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdFor)
  "#gen_spec_addr " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdForExtra)
  "#gen_spec_addr " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmd)
  "#gen_spec_addr_storage " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdExtra)
  "#gen_spec_addr_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdFor)
  "#gen_spec_addr_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdForExtra)
  "#gen_spec_addr_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2Cmd)
  "#gen_spec_addr_storage2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdExtra)
  "#gen_spec_addr_storage2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdFor)
  "#gen_spec_addr_storage2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdForExtra)
  "#gen_spec_addr_storage2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmd)
  "#gen_spec_map " ident
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdExtra)
  "#gen_spec_map " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor)
  "#gen_spec_map " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdForExtra)
  "#gen_spec_map " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor2)
  "#gen_spec_map " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor2Extra)
  "#gen_spec_map " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmd)
  "#gen_spec_map_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdExtra)
  "#gen_spec_map_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor)
  "#gen_spec_map_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdForExtra)
  "#gen_spec_map_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2)
  "#gen_spec_map_storage " ident " for "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2Alt)
  "#gen_spec_map_storage " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2Extra)
  "#gen_spec_map_storage " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2Cmd)
  "#gen_spec_map2 " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdExtra)
  "#gen_spec_map2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor)
  "#gen_spec_map2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdForExtra)
  "#gen_spec_map2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor2)
  "#gen_spec_map2 " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor2Extra)
  "#gen_spec_map2 " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor3)
  "#gen_spec_map2 " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor3Extra)
  "#gen_spec_map2 " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

macro_rules
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident ($slot:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value $frame s s')
  | `(#gen_spec_addr $name:ident ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value $frame s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage $name:ident
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue $frame s s')
  | `(#gen_spec_addr_storage $name:ident
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue $frame s s')
  | `(#gen_spec_addr_storage $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage2 $name:ident
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2 $frame s s')
  | `(#gen_spec_addr_storage2 $name:ident
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage2 $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2 $frame s s')
  | `(#gen_spec_addr_storage2 $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident
      ($slot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value $frame s s')
  | `(#gen_spec_map $name:ident
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $mapSlot $key $value $frame s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value $frame s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident for
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            $frame s s')
  | `(#gen_spec_map_storage $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')

end Verity.Macro
