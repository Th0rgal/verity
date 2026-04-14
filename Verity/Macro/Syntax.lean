import Lean

namespace Verity.Macro

open Lean

declare_syntax_cat verityStorageField
declare_syntax_cat verityStructMember
declare_syntax_cat verityParam
declare_syntax_cat verityError
declare_syntax_cat verityConstant
declare_syntax_cat verityImmutable
declare_syntax_cat verityExternal
declare_syntax_cat verityLocalObligation
declare_syntax_cat verityLocalObligations
declare_syntax_cat verityConstructor
declare_syntax_cat verityMutability
declare_syntax_cat verityInitGuard
declare_syntax_cat verityModifies
declare_syntax_cat verityRequiresRole
declare_syntax_cat verityNewtype
declare_syntax_cat verityAdtVariant
declare_syntax_cat verityAdtDecl
declare_syntax_cat verityNamespaceSpec
declare_syntax_cat veritySpecialEntrypoint
declare_syntax_cat verityFunction

syntax ident " : " term " := " "slot" num : verityStorageField
syntax ident " @word " num : verityStructMember
syntax ident " @word " num " packed(" num "," num ")" : verityStructMember
syntax "MappingStruct(" term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax "MappingStruct2(" term "," term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax ident " : " term : verityParam
syntax "error " ident "(" sepBy(term, ",") ")" : verityError
syntax ident " : " term:max " := " term:max : verityConstant
syntax ident " : " term:max " := " term:max : verityImmutable
syntax "external " ident "(" sepBy(term, ",") ")" (" -> " "(" sepBy(term, ",") ")")? : verityExternal
syntax ident " := " ident ppSpace str : verityLocalObligation
syntax "local_obligations " "[" sepBy(verityLocalObligation, ",") "]" : verityLocalObligations
syntax "payable" : verityMutability
syntax "view" : verityMutability
syntax "no_external_calls" : verityMutability
syntax "allow_post_interaction_writes" : verityMutability
syntax "nonreentrant(" ident ")" : verityMutability
syntax "cei_safe" : verityMutability
syntax "modifies(" sepBy1(ident, ",") ")" : verityModifies
syntax "requires(" ident ")" : verityRequiresRole
syntax ident " : " term:max : verityNewtype
syntax "| " ident "(" sepBy(verityParam, ",") ")" : verityAdtVariant
syntax "| " ident : verityAdtVariant
syntax ident " := " verityAdtVariant+ : verityAdtDecl
syntax "storage_namespace " : verityNamespaceSpec
syntax "storage_namespace " str : verityNamespaceSpec
syntax "initializer(" ident ")" : verityInitGuard
syntax "reinitializer(" ident ", " num ")" : verityInitGuard
syntax "ecmCall " term:max ppSpace term:max : term
syntax "ecmDo " term:max ppSpace term:max : term
syntax "tryCatch " term:max ppSpace term:max : doElem
syntax "revert " ident "(" sepBy(term, ",") ")" : doElem
syntax "revertError " ident "(" sepBy(term, ",") ")" : doElem
syntax "requireError " term:max ppSpace ident "(" sepBy(term, ",") ")" : doElem
syntax (priority := high) "unsafe " str " do " doSeq : doElem
syntax "constructor " "(" sepBy(verityParam, ",") ")" (ppSpace verityLocalObligations)? " := " term : verityConstructor
syntax "constructor " "(" sepBy(verityParam, ",") ")" " payable" (ppSpace verityLocalObligations)? " := " term : verityConstructor
syntax "receive" (ppSpace verityLocalObligations)? " := " term : veritySpecialEntrypoint
syntax "fallback" (ppSpace verityLocalObligations)? " := " term : veritySpecialEntrypoint
syntax "function " verityMutability* ident " (" sepBy(verityParam, ",") ")" (ppSpace verityInitGuard)? (ppSpace verityRequiresRole)? (ppSpace verityModifies)? (ppSpace verityLocalObligations)? " : " term " := " term : verityFunction

syntax (name := verityContractCmd)
  "verity_contract " ident " where "
  ("types " verityNewtype+)?
  ("inductive " verityAdtDecl+)?
  (verityNamespaceSpec)?
  "storage " verityStorageField*
  ("errors " verityError+)?
  ("constants " verityConstant+)?
  ("immutables " verityImmutable+)?
  ("linked_externals " verityExternal+)?
  (verityConstructor)?
  (veritySpecialEntrypoint)*
  verityFunction* : command

syntax (name := checkContractCmd)
  "#check_contract " ident : command

end Verity.Macro
