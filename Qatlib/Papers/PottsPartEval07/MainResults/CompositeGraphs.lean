/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Composition of weight enumerators

Weight enumerators with additive weights factor over products of finite codeword types. The
record `ExactEvaluator` stores a cost and a correctness proposition, and its `directSum`
construction adds costs and conjoins those propositions for the product weight
[GeraciLidar2008].

## Main statements

* `weightEnumerator_directSum`: Enumerators multiply when component weights add.
* `corollary1_directSum`: Component evaluator records combine with additive cost and inherited
  correctness.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.CompositeGraphs

open scoped BigOperators

/-- The univariate weight enumerator obtained by summing `t ^ w c` over a finite type. -/
def weightEnumerator {C : Type*} [Fintype C] {R : Type*} [CommSemiring R]
    (w : C → ℕ) (t : R) : R :=
  ∑ c : C, t ^ (w c)

/-- The weight enumerator for the sum of two component weights on a product type factors as the
product of their enumerators [GeraciLidar2008]. -/
theorem weightEnumerator_directSum {R : Type*} [CommSemiring R]
    {C1 C2 : Type*} [Fintype C1] [Fintype C2]
    (w1 : C1 → ℕ) (w2 : C2 → ℕ) (t : R) :
    (∑ p : C1 × C2, t ^ (w1 p.1 + w2 p.2)) =
      (∑ a : C1, t ^ w1 a) * (∑ b : C2, t ^ w2 b) := by
  rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
  simp_rw [pow_add]

/-- A record of a natural-number cost and a correctness proposition, indexed by a codeword type
and weight function. -/
structure ExactEvaluator (C : Type*) (w : C → ℕ) where

  cost : ℕ

  correct : Prop

namespace ExactEvaluator

/-- Combines two evaluator records for the sum weight, adding their costs and conjoining their
correctness propositions. -/
def directSum {C1 C2 : Type*} (w1 : C1 → ℕ) (w2 : C2 → ℕ)
    (s1 : ExactEvaluator C1 w1) (s2 : ExactEvaluator C2 w2) :
    ExactEvaluator (C1 × C2) (fun p => w1 p.1 + w2 p.2) where
  cost := s1.cost + s2.cost
  correct := s1.correct ∧ s2.correct

end ExactEvaluator

/-- There is a combined evaluator record with the sum of component costs whose correctness
follows from both component correctness propositions [GeraciLidar2008]. -/
theorem corollary1_directSum {C1 C2 : Type*}
    (w1 : C1 → ℕ) (w2 : C2 → ℕ)
    (s1 : ExactEvaluator C1 w1) (s2 : ExactEvaluator C2 w2) :
    ∃ s : ExactEvaluator (C1 × C2) (fun p => w1 p.1 + w2 p.2),
      s.cost = s1.cost + s2.cost ∧ (s1.correct → s2.correct → s.correct) :=
  ⟨ExactEvaluator.directSum w1 w2 s1 s2, rfl, fun h1 h2 => ⟨h1, h2⟩⟩

end Qatlib.Papers.PottsPartEval07.MainResults.CompositeGraphs
