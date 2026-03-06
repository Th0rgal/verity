namespace Compiler

def canonicalModules : List String :=
  [ "Contracts.SimpleStorage.SimpleStorage"
  , "Contracts.Counter.Counter"
  , "Contracts.Owned.Owned"
  , "Contracts.Ledger.Ledger"
  , "Contracts.OwnedCounter.OwnedCounter"
  , "Contracts.SimpleToken.SimpleToken"
  , "Contracts.SafeCounter.SafeCounter"
  , "Contracts.ERC20.ERC20"
  , "Contracts.ERC721.ERC721"
  ]

def contractNameOfModule (moduleName : String) : String :=
  match moduleName.splitOn "." |>.reverse with
  | name :: _ => name
  | [] => moduleName

end Compiler
