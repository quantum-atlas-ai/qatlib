/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable def observedMetadataScore
    {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (score : Bool → List (ℕ × ℕ) → ℝ) : ℝ :=
  ((observedTraces O P ψ).map fun t =>
    score t.accepted t.outcomes * branchMass t.state).sum

open scoped Matrix.Norms.L2Operator

def PairedExpectedHybridSpecification : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A B : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I),
    A ∈ Matrix.unitaryGroup I ℂ →
    B ∈ Matrix.unitaryGroup I ℂ →
    observedWellFormed P → Normalized ψ →
    let pairs := observedPairedTraces A B P ψ ψ
    let D2 := (pairs.map fun t =>
      ‖toEuclidean_fromVec (t.1.state - t.2.state)‖ ^ 2).sum
    let q := Real.sqrt
      (expectedObservedQueries A P ψ * expectedObservedQueries B P ψ)
    D2 ≤ 2 * ‖A - B‖ * q ∧
    (∀ score : Bool → List (ℕ × ℕ) → ℝ,
      (∀ b record, |score b record| ≤ 1) →
      (observedMetadataScore A P ψ score -
        observedMetadataScore B P ψ score) ^ 2 ≤
          8 * ‖A - B‖ * q) ∧
    (∀ (score : Bool → List (ℕ × ℕ) → ℝ) (γ Q : ℝ),
      (∀ b record, |score b record| ≤ 1) → 0 ≤ γ →
      expectedObservedQueries A P ψ ≤ Q →
      expectedObservedQueries B P ψ ≤ Q →
      2 * γ ≤ |observedMetadataScore A P ψ score -
        observedMetadataScore B P ψ score| →
      γ ^ 2 ≤ 2 * ‖A - B‖ * Q)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
