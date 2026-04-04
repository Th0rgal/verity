/-
  Contracts.UniswapV2.Display: Intent specification for the Uniswap V2 Router.

  Defines `Contracts.UniswapV2.intentSpec` — the provable intent DSL mapping
  for the Uniswap V2 Router's swap functions:
    - swapExactTokensForTokens(amountIn, amountOutMin, to)

  Note: The `path` and `deadline` parameters are not included in the intent
  spec because array types are not yet supported in Phase 1 of the DSL.
  The tokenIn/tokenOut resolution is handled by the frontend's address
  resolver using the decoded path array.
-/
import Verity.Intent.DSL

namespace Contracts.UniswapV2

open Verity.Intent
open Verity.Intent.DSL
open Compiler.CompilationModel (ParamType)

/-- Intent specification for the Uniswap V2 Router.

    Covers swapExactTokensForTokens with the core swap parameters.
    The path array (tokenIn → tokenOut routing) is decoded separately
    by the frontend for display purposes. -/
intent_spec "UniswapV2Router" where

  intent swapExactTokensForTokens(amountIn : uint256, amountOutMin : uint256, to : address) where
    emit "Swap {amountIn:tokenAmount 18} for at least {amountOutMin:tokenAmount 6}, send to {to:address}"

end Contracts.UniswapV2
