-- Verity Framework — imports core, EVM, macro, stdlib, and proof automation.
-- For examples, specs, and per-contract proofs, use `import Verity.All`.
import Verity.Core
import Verity.Core.Semantics
import Verity.Core.Uint256
import Verity.Core.FiniteSet
import Verity.Core.Free.TypedIR
import Verity.Core.Free.ContractStep
import Verity.Core.Free.TypedIRCompiler
import Verity.Core.Free.TypedIRCompilerCorrectness
import Verity.Core.Free.TypedIRLowering
import Verity.EVM.Uint256
import Verity.Stdlib.Math
import Verity.Macro
import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.MappingAutomation
import Verity.Proofs.Stdlib.ListSum
