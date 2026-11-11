/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity

/-!
# Bundled fixed-space query algorithms

The structure `QueryAlgorithm` bundles a query circuit with a normalized initial state and
unitary non-query gates. Its execution remains normalized for a unitary oracle.

The module relates this bundled formulation to `FixedSpaceQueryUpperBound`, retaining the error
range, oracle unitarity, query budget, and solution predicate of the quantum query model
discussed in [BealsEtAl2001].

## Main statements

* `QueryAlgorithm.normalized_output`: A bundled algorithm preserves normalization for a unitary
  oracle.
* `fixedSpaceQueryUpperBound_iff_queryAlgorithm`: Characterizes a fixed-space upper bound by a
  bundled algorithm.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- A query circuit bundled with a normalized initial state and a proof that its non-query gates
are unitary. -/
structure QueryAlgorithm where
  circuit : Circuit I
  start : QState I
  unitary : IsUnitaryCircuit circuit
  normalized : Normalized start

variable {I} {F : Type*}

/-- Running a query algorithm with a unitary oracle produces a normalized output state. -/
theorem QueryAlgorithm.normalized_output (A : QueryAlgorithm I)
    {O : Matrix I I ℂ} (hO : O ∈ Matrix.unitaryGroup I ℂ) :
    Normalized (Run O A.circuit A.start) := A.unitary.normalized_run hO A.normalized

/-- A query algorithm within budget `k` that solves the specified task with error `ε`
establishes the fixed-space upper bound when the error range and oracle unitarity conditions
hold. -/
theorem QueryAlgorithm.queryUpperBound (A : QueryAlgorithm I)
    {O : F → Matrix I I ℂ} {Acc : F → Finset I} {ε : ℝ} {k : ℕ}
    (hε : 0 ≤ ε ∧ ε < 1) (hO : ∀ f, O f ∈ Matrix.unitaryGroup I ℂ)
    (hcount : QueryCount A.circuit ≤ k)
    (hsolve : SolvesWithError O Acc A.circuit A.start ε) :
    FixedSpaceQueryUpperBound O Acc ε k :=
  ⟨hε, hO, A.circuit, A.start, A.unitary, A.normalized, hcount, hsolve⟩

/-- A fixed-space query upper bound is equivalent to the error range and oracle unitarity
conditions together with a bundled algorithm meeting the query budget and error
specification. -/
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
