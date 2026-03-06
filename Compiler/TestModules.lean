namespace Compiler

def canonicalModules : List String :=
  [ "Contracts.MacroContracts.SimpleStorage"
  , "Contracts.MacroContracts.Counter"
  , "Contracts.MacroContracts.Owned"
  , "Contracts.MacroContracts.Ledger"
  , "Contracts.MacroContracts.OwnedCounter"
  , "Contracts.MacroContracts.SimpleToken"
  , "Contracts.MacroContracts.SafeCounter"
  , "Contracts.MacroContracts.ERC20"
  , "Contracts.MacroContracts.ERC721"
  ]

def contractNameOfModule (moduleName : String) : String :=
  match moduleName.splitOn "." |>.reverse with
  | name :: _ => name
  | [] => moduleName

end Compiler
