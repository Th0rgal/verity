import Compiler.Proofs.YulGeneration.RuntimeTypes

namespace Compiler.Proofs.YulGeneration

/-!
Compatibility re-export for historical imports.

`YulState` now lives in `Compiler.Proofs.YulGeneration.RuntimeTypes` so native
EVMYulLean proofs can use the shared state shape without importing a
reference-oracle module.
-/

end Compiler.Proofs.YulGeneration
