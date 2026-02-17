/-
  Verity.Proofs.Stdlib.AuthorizationAutomation

  Automation lemmas for authorization patterns (require, msgSender, access control).
  These lemmas help prove properties about authorization checks.

  Status: All lemmas fully proven with zero sorry.
-/

import Verity.Core
import Verity.Proofs.Stdlib.Automation

namespace Verity.Proofs.Stdlib.AuthorizationAutomation

open Verity
open Verity.Proofs.Stdlib.Automation

/-!
## Authorization State Lemmas
-/

theorem msgSender_runState (state : ContractState) :
    msgSender.runState state = state :=
  Automation.msgSender_runState state

theorem msgSender_runValue (state : ContractState) :
    msgSender.runValue state = state.sender :=
  Automation.msgSender_runValue state

/-!
## require Lemmas
-/

theorem require_true_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = true) :
    ((require cond msg).run state).isSuccess = true :=
  Automation.require_true_isSuccess cond msg state h

theorem require_false_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = false) :
    ((require cond msg).run state).isSuccess = false :=
  Automation.require_false_isSuccess cond msg state h

theorem require_success_implies_cond (cond : Bool) (msg : String) (state : ContractState) :
    ((require cond msg).run state).isSuccess = true →
    cond = true :=
  Automation.require_success_implies_cond cond msg state

end Verity.Proofs.Stdlib.AuthorizationAutomation
