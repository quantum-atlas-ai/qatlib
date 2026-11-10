/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Order.Real

set_option autoImplicit false

open scoped NNReal ENNReal BigOperators

namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

noncomputable def erasureMask (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : PMF (Fin n → Bool) :=
  PMF.ofFintype (fun mask => ∏ i, PMF.bernoulli p hp (mask i)) (by
    rw [← Fintype.prod_sum]
    have hs : ∑ b : Bool, PMF.bernoulli p hp b = 1 := by
      simpa only [tsum_fintype] using (PMF.bernoulli p hp).tsum_coe
    simp only [hs, Finset.prod_const_one])

theorem erasureMask_apply (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (mask : Fin n → Bool) :
    erasureMask n p hp mask = ∏ i, PMF.bernoulli p hp (mask i) := rfl

theorem erasureMask_complete (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    erasureMask n p hp (fun _ => true) = (p : ℝ≥0∞)^n := by
  simp [erasureMask_apply, PMF.bernoulli_apply]

theorem erasureMask_complete_event (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (erasureMask n p hp).toOuterMeasure {mask | mask = (fun _ => true)} = (p : ℝ≥0∞)^n := by
  rw [show {mask : Fin n → Bool | mask = (fun _ => true)} = {(fun _ => true)} by rfl,
    PMF.toOuterMeasure_apply_singleton, erasureMask_complete]

theorem bind_success_le {A : Type*} (p : PMF A) (next : A → PMF Bool)
    (B : ℝ≥0∞) (h : ∀ a, next a true ≤ B) : (p.bind next) true ≤ B := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' a, p a * B := ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) _)
    _ = B := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
