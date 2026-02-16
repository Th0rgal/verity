/-
  Compiler.Specs: Declarative Contract Specifications

  This file demonstrates the new declarative contract specification system.
  Each contract is specified once, and IR is generated automatically.

  This replaces the manual IR definitions in Translate.lean.
-/

import Compiler.ContractSpec

namespace Compiler.Specs

open Compiler.ContractSpec

/-!
## Shared Helpers
-/

def requireOwner : Stmt :=
  Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"

/-- Transfer body for mapping-based balance contracts.
    Handles self-transfer safely by computing a zero delta when caller == to. -/
@[reducible] def transferBody (mappingName : String) : List Stmt := [
  -- Pre-load both balances to match EDSL semantics (prevents self-transfer bug)
  Stmt.letVar "senderBal" (Expr.mapping mappingName Expr.caller),
  Stmt.letVar "recipientBal" (Expr.mapping mappingName (Expr.param "to")),
  Stmt.require
    (Expr.ge (Expr.localVar "senderBal") (Expr.param "amount"))
    "Insufficient balance",
  -- If caller == to, delta = 0 so both updates become no-ops.
  Stmt.letVar "sameAddr" (Expr.eq Expr.caller (Expr.param "to")),
  Stmt.letVar "delta" (Expr.sub (Expr.literal 1) (Expr.localVar "sameAddr")),
  Stmt.letVar "amountDelta" (Expr.mul (Expr.param "amount") (Expr.localVar "delta")),
  -- Overflow check: newRecipientBal must be >= recipientBal (wrapping add overflow detection)
  Stmt.letVar "newRecipientBal" (Expr.add (Expr.localVar "recipientBal") (Expr.localVar "amountDelta")),
  Stmt.require (Expr.ge (Expr.localVar "newRecipientBal") (Expr.localVar "recipientBal")) "Recipient balance overflow",
  Stmt.setMapping mappingName Expr.caller
    (Expr.sub (Expr.localVar "senderBal") (Expr.localVar "amountDelta")),
  Stmt.setMapping mappingName (Expr.param "to") (Expr.localVar "newRecipientBal"),
  Stmt.stop
]

/-!
## SimpleStorage Specification
-/

def simpleStorageSpec : ContractSpec := {
  name := "SimpleStorage"
  fields := [
    { name := "storedData", ty := FieldType.uint256 }
  ]
  constructor := none  -- No initialization needed
  functions := [
    { name := "store"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "storedData" (Expr.param "value"),
        Stmt.stop
      ]
    },
    { name := "retrieve"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "storedData")
      ]
    }
  ]
}


/-!
## Counter Specification
-/

def counterSpec : ContractSpec := {
  name := "Counter"
  fields := [
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := none
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    }
  ]
}


/-!
## Owned Specification
-/

def ownedSpec : ContractSpec := {
  name := "Owned"
  fields := [
    { name := "owner", ty := FieldType.address }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0)
    ]
  }
  functions := [
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "owner" (Expr.param "newOwner"),
        Stmt.stop
      ]
    },
    { name := "getOwner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}


/-!
## Ledger Specification
-/

def ledgerSpec : ContractSpec := {
  name := "Ledger"
  fields := [
    { name := "balances", ty := FieldType.mapping }
  ]
  constructor := none
  functions := [
    { name := "deposit"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "senderBal" (Expr.mapping "balances" Expr.caller),
        Stmt.setMapping "balances" Expr.caller
          (Expr.add (Expr.localVar "senderBal") (Expr.param "amount")),
        Stmt.stop
      ]
    },
    { name := "withdraw"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "senderBal" (Expr.mapping "balances" Expr.caller),
        Stmt.require
          (Expr.ge (Expr.localVar "senderBal") (Expr.param "amount"))
          "Insufficient balance",
        Stmt.setMapping "balances" Expr.caller
          (Expr.sub (Expr.localVar "senderBal") (Expr.param "amount")),
        Stmt.stop
      ]
    },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := transferBody "balances"
    },
    { name := "getBalance"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    }
  ]
}


/-!
## OwnedCounter Specification (Combines Owned + Counter)
-/

def ownedCounterSpec : ContractSpec := {
  name := "OwnedCounter"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0)
    ]
  }
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    },
    { name := "getOwner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    },
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "owner" (Expr.param "newOwner"),
        Stmt.stop
      ]
    }
  ]
}


/-!
## SimpleToken Specification (Owned + Balances + Supply)
-/

def simpleTokenSpec : ContractSpec := {
  name := "SimpleToken"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "balances", ty := FieldType.mapping },
    { name := "totalSupply", ty := FieldType.uint256 }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0),
      Stmt.setStorage "totalSupply" (Expr.literal 0)
    ]
  }
  functions := [
    { name := "mint"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        requireOwner,
        Stmt.letVar "recipientBal" (Expr.mapping "balances" (Expr.param "to")),
        Stmt.letVar "newBalance" (Expr.add (Expr.localVar "recipientBal") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newBalance") (Expr.localVar "recipientBal")) "Balance overflow",
        Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newBalance"),
        Stmt.letVar "supply" (Expr.storage "totalSupply"),
        Stmt.letVar "newSupply" (Expr.add (Expr.localVar "supply") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newSupply") (Expr.localVar "supply")) "Supply overflow",
        Stmt.setStorage "totalSupply" (Expr.localVar "newSupply"),
        Stmt.stop
      ]
    },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := transferBody "balances"
    },
    { name := "balanceOf"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    },
    { name := "totalSupply"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "totalSupply")
      ]
    },
    { name := "owner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}


/-!
## Note: CryptoHash Specification Example
External function linking is demonstrated via the example libraries in
`examples/external-libs/` and the CLI usage. A full CryptoHashSpec
could be added here when ready for production use.
-/


/-!
## SafeCounter Specification (Counter with overflow/underflow checks)
-/
def safeCounterSpec : ContractSpec := {
  name := "SafeCounter"
  fields := [
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := none
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        -- Overflow check: require (count + 1 > count)
        -- On overflow, MAX_UINT + 1 = 0, which is NOT > MAX_UINT, so this will revert
        Stmt.letVar "count" (Expr.storage "count"),
        Stmt.letVar "newCount" (Expr.add (Expr.localVar "count") (Expr.literal 1)),
        Stmt.require (Expr.gt (Expr.localVar "newCount") (Expr.localVar "count")) "Overflow in increment",
        Stmt.setStorage "count" (Expr.localVar "newCount"),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.letVar "count" (Expr.storage "count"),
        Stmt.require (Expr.ge (Expr.localVar "count") (Expr.literal 1)) "Underflow in decrement",
        Stmt.setStorage "count" (Expr.sub (Expr.localVar "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    }
  ]
}


/-!
## Generate All Contracts
-/

def allSpecs : List ContractSpec := [
  simpleStorageSpec,
  counterSpec,
  ownedSpec,
  ledgerSpec,
  ownedCounterSpec,
  simpleTokenSpec,
  safeCounterSpec
]

end Compiler.Specs
