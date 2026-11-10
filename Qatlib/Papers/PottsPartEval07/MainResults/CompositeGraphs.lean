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

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.CompositeGraphs

open scoped BigOperators

def weightEnumerator {C : Type*} [Fintype C] {R : Type*} [CommSemiring R]
    (w : C → ℕ) (t : R) : R :=
  ∑ c : C, t ^ (w c)

theorem weightEnumerator_directSum {R : Type*} [CommSemiring R]
    {C1 C2 : Type*} [Fintype C1] [Fintype C2]
    (w1 : C1 → ℕ) (w2 : C2 → ℕ) (t : R) :
    (∑ p : C1 × C2, t ^ (w1 p.1 + w2 p.2)) =
      (∑ a : C1, t ^ w1 a) * (∑ b : C2, t ^ w2 b) := by
  rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
  simp_rw [pow_add]

structure ExactEvaluator (C : Type*) (w : C → ℕ) where

  cost : ℕ

  correct : Prop

namespace ExactEvaluator

def directSum {C1 C2 : Type*} (w1 : C1 → ℕ) (w2 : C2 → ℕ)
    (s1 : ExactEvaluator C1 w1) (s2 : ExactEvaluator C2 w2) :
    ExactEvaluator (C1 × C2) (fun p => w1 p.1 + w2 p.2) where
  cost := s1.cost + s2.cost
  correct := s1.correct ∧ s2.correct

end ExactEvaluator

theorem corollary1_directSum {C1 C2 : Type*}
    (w1 : C1 → ℕ) (w2 : C2 → ℕ)
    (s1 : ExactEvaluator C1 w1) (s2 : ExactEvaluator C2 w2) :
    ∃ s : ExactEvaluator (C1 × C2) (fun p => w1 p.1 + w2 p.2),
      s.cost = s1.cost + s2.cost ∧ (s1.correct → s2.correct → s.correct) :=
  ⟨ExactEvaluator.directSum w1 w2 s1 s2, rfl, fun h1 h2 => ⟨h1, h2⟩⟩

end Qatlib.Papers.PottsPartEval07.MainResults.CompositeGraphs
