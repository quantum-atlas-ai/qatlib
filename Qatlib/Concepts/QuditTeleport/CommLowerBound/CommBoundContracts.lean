/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Contracts for teleportation message lower bounds

`mergedQuditBranch` and `mergedBellBranch` combine two teleportation outcomes under one
correction. The four contracts express impossibility of exact merged recovery and injectivity of
message assignments for unitary corrections, in qudit and Bell protocols. The contracts address
the classical communication requirement of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `CommBoundMergeNoGoQudit`: The proposition that merging distinct qudit outcomes under one
  correction fails to equal `2 / n²` times the identity map on some finite extension.
* `CommBoundMessageInjectiveQudit`: The proposition that exact qudit recovery with unitary
  corrections forces the outcome-to-message map to be injective and the message alphabet to
  contain at least `n²` elements.
* `CommBoundMessageInjectiveBell`: The proposition that exact Bell recovery with unitary
  corrections forces an injective outcome-to-message map and at least four message labels.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.CommLowerBound

open Qatlib

/-- The sum of two qudit teleportation branches after applying the same correction matrix `C`. -/
noncomputable def mergedQuditBranch (n : ℕ) [NeZero n] (o o' : Fin n × Fin n)
    (C : Operator n) : Operator n →ₗ[ℂ] Operator n :=
  conjBranch (C * quditBranchKraus n o) + conjBranch (C * quditBranchKraus n o')

/-- The sum of two Bell teleportation branches after applying the same correction matrix `C`. -/
noncomputable def mergedBellBranch (o o' : Bool × Bool) (C : Operator 2) :
    Operator 2 →ₗ[ℂ] Operator 2 :=
  conjBranch (C * teleportBranchKraus o) + conjBranch (C * teleportBranchKraus o')

/-- The proposition that merging distinct qudit outcomes under one correction fails to equal `2
/ n²` times the identity map on some finite extension. -/
def CommBoundMergeNoGoQudit : Prop :=
  ∀ (n : ℕ) [NeZero n] (o o' : Fin n × Fin n), o ≠ o' → ∀ C : Operator n,
    ∃ (R : ℕ) (X : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ),
      tensorLeft (mergedQuditBranch n o o' C) X ≠ (2 / (n : ℂ) ^ 2) • X

/-- The proposition that exact qudit recovery with unitary corrections forces the
outcome-to-message map to be injective and the message alphabet to contain at least `n²`
elements. -/
def CommBoundMessageInjectiveQudit : Prop :=
  ∀ (n : ℕ) [NeZero n] (κ : Type) [Fintype κ] (m : Fin n × Fin n → κ)
    (Cm : κ → Operator n),
    (∀ a, Cm a ∈ Matrix.unitaryGroup (Fin n) ℂ) →
    (∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) →
      Function.Injective m ∧ n * n ≤ Fintype.card κ

/-- The proposition that merging distinct Bell outcomes under one correction fails to equal half
the identity map on some finite extension. -/
def CommBoundMergeNoGoBell : Prop :=
  ∀ (o o' : Bool × Bool), o ≠ o' → ∀ C : Operator 2,
    ∃ (R : ℕ) (X : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ),
      tensorLeft (mergedBellBranch o o' C) X ≠ (1 / 2 : ℂ) • X

/-- The proposition that exact Bell recovery with unitary corrections forces an injective
outcome-to-message map and at least four message labels. -/
def CommBoundMessageInjectiveBell : Prop :=
  ∀ (κ : Type) [Fintype κ] (m : Bool × Bool → κ) (Cm : κ → Operator 2),
    (∀ a, Cm a ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
    (∀ ρ : Operator 2,
      (∑ o : Bool × Bool, conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) →
      Function.Injective m ∧ Fintype.card (Bool × Bool) ≤ Fintype.card κ

end Qatlib.Concepts.QuditTeleport.CommLowerBound
