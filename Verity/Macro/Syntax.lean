import Lean

namespace Verity.Macro

open Lean

declare_syntax_cat verityStorageField
declare_syntax_cat verityStructMember
declare_syntax_cat verityParam
declare_syntax_cat verityConstructor
declare_syntax_cat verityFunction

syntax ident " : " term " := " "slot" num : verityStorageField
syntax ident " @word " num : verityStructMember
syntax ident " @word " num " packed(" num "," num ")" : verityStructMember
syntax "MappingStruct(" term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax "MappingStruct2(" term "," term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax ident " : " term : verityParam
syntax "constructor " "(" sepBy(verityParam, ",") ")" " := " term : verityConstructor
syntax "function " ident " (" sepBy(verityParam, ",") ")" " : " term " := " term : verityFunction

syntax (name := verityContractCmd)
  "verity_contract " ident " where "
  "storage " verityStorageField+
  (verityConstructor)?
  verityFunction+ : command

syntax (name := checkContractCmd)
  "#check_contract " ident : command

end Verity.Macro
