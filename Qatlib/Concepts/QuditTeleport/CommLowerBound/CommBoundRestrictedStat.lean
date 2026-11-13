/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundContracts

/-!
# Restricted teleportation communication bounds

`CommBoundRestricted` collects the qudit and Bell contracts for merged-branch impossibility and
message injectivity. The message-injectivity clauses assume unitary corrections. The contracts
address the classical communication requirement of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `CommBoundRestricted`: The conjunction of the qudit and Bell merged-branch impossibility
  contracts and the corresponding message-injectivity contracts with unitary corrections.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.QuditTeleport.CommLowerBound

/-- The conjunction of the qudit and Bell merged-branch impossibility contracts and the
corresponding message-injectivity contracts with unitary corrections. -/
def CommBoundRestricted : Prop :=
  CommBoundMergeNoGoQudit ∧ CommBoundMessageInjectiveQudit ∧
    CommBoundMergeNoGoBell ∧ CommBoundMessageInjectiveBell
end Qatlib.Concepts.QuditTeleport.CommLowerBound
