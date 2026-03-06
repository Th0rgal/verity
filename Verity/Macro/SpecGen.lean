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

end Verity.Macro
