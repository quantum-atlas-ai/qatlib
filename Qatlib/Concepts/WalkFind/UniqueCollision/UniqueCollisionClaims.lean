/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolutionQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonDataQuan

/-!
# Collision-search claims and native algorithm interfaces

This module names full and restricted statements for the collision-search results in
[Ambainis2007ElementDistinctness]. `Theorem3Statement` expresses a correct randomized query
algorithm with the optimized query exponent, while `Theorem3RestrictedStatement` names the
thresholded reduced-search bound.

The proved declarations package the restricted query conclusions, the native unique-solution
theorem, and the native data-access and reduced-search interfaces for Algorithms 1 and 2.

## Main statements

* `theorem3_restricted`: the optimized reduced-search bound.
* `theorem4_restricted`: the conjunction of reduced-search and query bounds.
* `theorem5`: the native unique-solution conclusion.
* `algorithm1` and `algorithm2`: the native walk and reduced-search interfaces.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The proposition that for each `k ≥ 2`, a positive constant bounds every seed's query count
by `C*N^(k/(k+1))` for a correct collision algorithm on every positive input and alphabet
size [Ambainis2007ElementDistinctness]. -/
def Theorem3Statement : Prop :=
  ∀ (k : ℕ), 2 ≤ k →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M : ℕ) [NeZero M], 0 < N → 0 < M →
        ∃ A : Qatlib.Concepts.WalkFind.SearchAlgorithm.RandomQueryAlgorithm N M k,
          Qatlib.Concepts.WalkFind.SearchAlgorithm.algorithmCorrect A ∧
            ∀ s, (QueryCount (A.program s) : ℝ) ≤ C * (N : ℝ) ^ ((k : ℝ) / (k + 1))

/-- The restricted Theorem 3 proposition, defined to be the thresholded reduced-search statement
`QueryComplexity` [Ambainis2007ElementDistinctness]. -/
def Theorem3RestrictedStatement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexity

/-- The restricted Theorem 3 statement holds through `queryComplexity_answer`
[Ambainis2007ElementDistinctness]. -/
theorem theorem3_restricted : Theorem3RestrictedStatement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.queryComplexity_answer

/-- The general query-memory proposition `GeneralQueryMemoryContract`, associated with the
tradeoff in [Ambainis2007ElementDistinctness]. -/
def Theorem4Statement : Prop :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.GeneralQueryMemoryContract

/-- The restricted Theorem 4 proposition, requiring both `ElementDistinctnessAlgorithm` and
`QueryComplexity` [Ambainis2007ElementDistinctness]. -/
def Theorem4RestrictedStatement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithm ∧
    Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexity

/-- The reduced-search guarantee and the optimized query bound jointly establish the restricted
Theorem 4 statement [Ambainis2007ElementDistinctness]. -/
theorem theorem4_restricted : Theorem4RestrictedStatement :=
  ⟨Qatlib.Concepts.WalkFind.UniqueCollision.elementDistinctnessAlgorithm_answer,
    Qatlib.Concepts.WalkFind.UniqueCollision.queryComplexity_answer⟩

/-- The native unique-solution proposition `NativeSingleSolution`, corresponding to the
unique-collision search analysis in [Ambainis2007ElementDistinctness]. -/
def Theorem5Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolution

/-- The native unique-solution statement follows from `nativeSingleSolution_answer`
[Ambainis2007ElementDistinctness]. -/
theorem theorem5 : Theorem5Statement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.nativeSingleSolution_answer

/-- The native Johnson data-access proposition for the walk implementation associated with
Algorithm 1 in [Ambainis2007ElementDistinctness]. -/
def Algorithm1Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonData

/-- The native Johnson data-access implementation satisfies `Algorithm1Statement`
[Ambainis2007ElementDistinctness]. -/
theorem algorithm1 : Algorithm1Statement :=
  Qatlib.Concepts.WalkFind.UniqueCollision.nativeJohnsonData_answer

/-- The conjunction of native Johnson data access and the reduced element-distinctness search
guarantee, associated with Algorithm 2 in [Ambainis2007ElementDistinctness]. -/
def Algorithm2Statement : Prop :=
  Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonData ∧
    Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithm

/-- Native Johnson data access and the reduced-search guarantee jointly establish
`Algorithm2Statement` [Ambainis2007ElementDistinctness]. -/
theorem algorithm2 : Algorithm2Statement :=
  ⟨Qatlib.Concepts.WalkFind.UniqueCollision.nativeJohnsonData_answer,
    Qatlib.Concepts.WalkFind.UniqueCollision.elementDistinctnessAlgorithm_answer⟩

end Qatlib.Concepts.WalkFind.UniqueCollision
