import Verity.Core

namespace Verity

abbrev World := ContractState
abbrev Exit (α : Type) := ContractResult α

def Env.defaultCallOracle (_name : String) (args : List Uint256) : Uint256 :=
  args.foldl (fun acc arg => acc + arg) 0

structure Env where
  sender : Address
  thisAddress : Address
  msgValue : Uint256
  blockTimestamp : Uint256
  blockNumber : Uint256 := 0
  chainId : Uint256 := 0
  callOracle : String → List Uint256 → Uint256 := Env.defaultCallOracle

instance : Repr Env where
  reprPrec env _ :=
    s!"Env(sender={repr env.sender}, thisAddress={repr env.thisAddress}, msgValue={repr env.msgValue}, blockTimestamp={repr env.blockTimestamp}, blockNumber={repr env.blockNumber}, chainId={repr env.chainId}, callOracle=<fn>)"

def Env.ofWorld (w : World) : Env where
  sender := w.sender
  thisAddress := w.thisAddress
  msgValue := w.msgValue
  blockTimestamp := w.blockTimestamp
  blockNumber := w.blockNumber
  chainId := w.chainId

def World.withEnv (w : World) (env : Env) : World :=
  { w with
    sender := env.sender
    thisAddress := env.thisAddress
    msgValue := env.msgValue
    blockTimestamp := env.blockTimestamp
    blockNumber := env.blockNumber
    chainId := env.chainId
  }

end Verity
