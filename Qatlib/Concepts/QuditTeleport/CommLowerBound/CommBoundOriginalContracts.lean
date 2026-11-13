/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Legacy teleportation message-injectivity contracts

`CommBoundMessageInjectiveQuditLegacy` and `CommBoundMessageInjectiveBellLegacy` state
message-injectivity claims for exact recovery by arbitrary correction matrices. These legacy
contracts omit the unitary-correction hypotheses used in the corrected contracts. The contracts
address the classical communication requirement of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `CommBoundMessageInjectiveQuditLegacy`: The legacy proposition that exact qudit recovery with
  arbitrary correction matrices forces an injective message map and at least `n²` labels.
* `CommBoundMessageInjectiveBellLegacy`: The legacy proposition that exact Bell recovery with
  arbitrary correction matrices forces an injective message map and at least four labels.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib

/-- The legacy proposition that exact qudit recovery with arbitrary correction matrices forces
an injective message map and at least `n²` labels. -/
def CommBoundMessageInjectiveQuditLegacy : Prop :=
  ∀ (n : ℕ) [NeZero n] (κ : Type) [Fintype κ] (m : Fin n × Fin n → κ)
    (Cm : κ → Operator n),
    (∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) →
      Function.Injective m ∧ n * n ≤ Fintype.card κ

/-- The legacy proposition that exact Bell recovery with arbitrary correction matrices forces an
injective message map and at least four labels. -/
def CommBoundMessageInjectiveBellLegacy : Prop :=
  ∀ (κ : Type) [Fintype κ] (m : Bool × Bool → κ) (Cm : κ → Operator 2),
    (∀ ρ : Operator 2,
      (∑ o : Bool × Bool, conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) →
      Function.Injective m ∧ Fintype.card (Bool × Bool) ≤ Fintype.card κ

end Qatlib.Concepts.QuditTeleport.CommLowerBound
