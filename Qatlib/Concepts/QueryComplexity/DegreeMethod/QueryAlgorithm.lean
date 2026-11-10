/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

variable (I : Type*) [Fintype I] [DecidableEq I]

structure QueryAlgorithm where
  circuit : Circuit I
  start : QState I
  unitary : IsUnitaryCircuit circuit
  normalized : Normalized start

variable {I} {F : Type*}

theorem QueryAlgorithm.normalized_output (A : QueryAlgorithm I)
    {O : Matrix I I ℂ} (hO : O ∈ Matrix.unitaryGroup I ℂ) :
    Normalized (Run O A.circuit A.start) := A.unitary.normalized_run hO A.normalized

theorem QueryAlgorithm.queryUpperBound (A : QueryAlgorithm I)
    {O : F → Matrix I I ℂ} {Acc : F → Finset I} {ε : ℝ} {k : ℕ}
    (hε : 0 ≤ ε ∧ ε < 1) (hO : ∀ f, O f ∈ Matrix.unitaryGroup I ℂ)
    (hcount : QueryCount A.circuit ≤ k)
    (hsolve : SolvesWithError O Acc A.circuit A.start ε) :
    FixedSpaceQueryUpperBound O Acc ε k :=
  ⟨hε, hO, A.circuit, A.start, A.unitary, A.normalized, hcount, hsolve⟩

theorem fixedSpaceQueryUpperBound_iff_queryAlgorithm
    (O : F → Matrix I I ℂ) (Acc : F → Finset I) (ε : ℝ) (k : ℕ) :
    FixedSpaceQueryUpperBound O Acc ε k ↔
      (0 ≤ ε ∧ ε < 1) ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
        ∃ A : QueryAlgorithm I,
          QueryCount A.circuit ≤ k ∧ SolvesWithError O Acc A.circuit A.start ε := by
  constructor
  · rintro ⟨hε, hO, C, ψ, hC, hψ, hk, hs⟩
    exact ⟨hε, hO, ⟨C, ψ, hC, hψ⟩, hk, hs⟩
  · rintro ⟨hε, hO, A, hk, hs⟩
    exact A.queryUpperBound hε hO hk hs

end Qatlib.Concepts.QueryComplexity.DegreeMethod
