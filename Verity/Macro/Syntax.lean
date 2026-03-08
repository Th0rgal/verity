import Lean

namespace Verity.Macro

open Lean

declare_syntax_cat verityStorageField
declare_syntax_cat verityStructMember
declare_syntax_cat verityParam
declare_syntax_cat verityError
declare_syntax_cat verityConstant
declare_syntax_cat verityConstructor
declare_syntax_cat verityFunction

syntax ident " : " term " := " "slot" num : verityStorageField
syntax ident " @word " num : verityStructMember
syntax ident " @word " num " packed(" num "," num ")" : verityStructMember
syntax "MappingStruct(" term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax "MappingStruct2(" term "," term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax ident " : " term : verityParam
syntax "error " ident "(" sepBy(term, ",") ")" : verityError
syntax ident " : " term:max " := " term:max : verityConstant
syntax "revert " ident "(" sepBy(term, ",") ")" : doElem
syntax "revertError " ident "(" sepBy(term, ",") ")" : doElem
syntax "requireError " term:max ppSpace ident "(" sepBy(term, ",") ")" : doElem
syntax "constructor " "(" sepBy(verityParam, ",") ")" " := " term : verityConstructor
syntax "constructor " "(" sepBy(verityParam, ",") ")" " payable" " := " term : verityConstructor
syntax "function " ident " (" sepBy(verityParam, ",") ")" " : " term " := " term : verityFunction

syntax (name := verityContractCmd)
  "verity_contract " ident " where "
  "storage " verityStorageField*
  ("errors " verityError+)?
  ("constants " verityConstant+)?
  (verityConstructor)?
  verityFunction+ : command

syntax (name := checkContractCmd)
  "#check_contract " ident : command

end Verity.Macro
