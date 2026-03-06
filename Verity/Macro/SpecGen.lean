import Verity.Specs.Common

namespace Verity.Macro

set_option hygiene false

syntax (name := genSpecCmd)
  "#gen_spec " ident " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdExtra)
  "#gen_spec " ident " (" term ", " term ", " term ", " term ")" : command

macro_rules
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')

end Verity.Macro
