import Compiler.CompilationModel
import Contracts.Counter
import Contracts.SimpleStorage
import Contracts.Owned
import Contracts.OwnedCounter
import Contracts.SafeCounter
import Contracts.Ledger
import Contracts.SimpleToken
import Contracts.ERC20
import Contracts.ERC721

namespace Compiler.Specs

open Compiler.CompilationModel

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def simpleStorageSpec : CompilationModel := Contracts.SimpleStorage.spec

/-- Legacy compatibility shim preserving the historical 3-function Counter surface. -/
def counterSpec : CompilationModel :=
  let canonical := Contracts.Counter.spec
  { canonical with
    functions := canonical.functions.filter fun fn =>
      fn.name = "increment" || fn.name = "decrement" || fn.name = "getCount" }

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ownedSpec : CompilationModel := Contracts.Owned.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ledgerSpec : CompilationModel := Contracts.Ledger.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ownedCounterSpec : CompilationModel := Contracts.OwnedCounter.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def simpleTokenSpec : CompilationModel := Contracts.SimpleToken.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def safeCounterSpec : CompilationModel := Contracts.SafeCounter.spec

/-- ERC20 spec alias for test/proof convenience. Uses the macro-generated spec. -/
def erc20Spec : CompilationModel := Contracts.ERC20.spec

/-- ERC721 spec alias for test/proof convenience. Uses the macro-generated spec. -/
def erc721Spec : CompilationModel := Contracts.ERC721.spec

end Compiler.Specs
