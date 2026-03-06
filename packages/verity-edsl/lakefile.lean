import Lake
open Lake DSL

package «verity-edsl» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git"@"047f63070309f436b66c61e276ab3b6d1169265a"

lean_lib «Verity» where
  srcDir := "../.."
  globs := #[
    .one `Verity,
    .one `Compiler.Constants,
    .one `Compiler.Identifier,
    .one `Compiler.Hex,
    .one `Compiler.ECM,
    .one `Compiler.IR,
    .one `Compiler.Yul,
    .andSubmodules `Compiler.Yul,
    .one `Compiler.Modules,
    .andSubmodules `Compiler.Modules,
    .one `Compiler.ABI,
    .one `Compiler.Codegen,
    .one `Compiler.Linker,
    .one `Compiler.ModuleInput,
    .one `Compiler.Lowering.FromEDSL,
    .one `Compiler.CompileDriver,
    .one `Compiler.ParityPacks,
    .one `Compiler.Gas.StaticAnalysis,
    .one `Compiler.Main,
    .one `Compiler.CompilationModel,
    .andSubmodules `Compiler.CompilationModel,
    .one `Compiler.Selector
  ]
