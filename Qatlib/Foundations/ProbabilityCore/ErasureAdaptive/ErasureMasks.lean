/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.OuterMeasure.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

public import Qatlib.Foundations.ProbabilityCore.CoinLaw

@[expose] public section

/-!
# Independent Bernoulli erasure masks

The distribution `erasureMask` samples independent Boolean erasure indicators, with `true`
representing erasure. This module computes mask probabilities and complete-erasure mass, and
supplies a uniform bound for the success probability of a PMF bind; these facts support adaptive
erasure estimates [BhartiHaugTanggara2026].

## Main statements

* `erasureMask_apply`: A mask has the product of its Bernoulli coordinate masses.
* `erasureMask_complete_event`: The complete-erasure event has mass pⁿ.
* `bind_success_le`: A uniform continuation bound also bounds the bound distribution.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false

open scoped NNReal ENNReal BigOperators

namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- The distribution of `n` independent Bernoulli erasure indicators, each equal to `true` with
probability `p`. -/
noncomputable def erasureMask (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : PMF (Fin n → Bool) :=
  PMF.ofFintype (fun mask => ∏ i, Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli p hp (mask i)) (by
    rw [← Fintype.prod_sum]
    have hs : ∑ b : Bool, Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli p hp b = 1 := by
      simpa only [tsum_fintype] using (Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli p hp).tsum_coe
    simp only [hs, Finset.prod_const_one])

/-- The probability of a specified erasure mask is the product of the Bernoulli probabilities of
its coordinates. -/
theorem erasureMask_apply (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (mask : Fin n → Bool) :
    erasureMask n p hp mask = ∏ i, Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli p hp (mask i) := rfl

/-- The all-true mask, representing complete erasure, has probability `p ^ n`. -/
theorem erasureMask_complete (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    erasureMask n p hp (fun _ => true) = (p : ℝ≥0∞)^n := by
  simp [erasureMask_apply, Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli_apply]

/-- The outer-measure mass of the complete-erasure event is `p ^ n`. -/
theorem erasureMask_complete_event (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (erasureMask n p hp).toOuterMeasure {mask | mask = (fun _ => true)} = (p : ℝ≥0∞)^n := by
  rw [show {mask : Fin n → Bool | mask = (fun _ => true)} = {(fun _ => true)} by rfl,
    PMF.toOuterMeasure_apply_singleton, erasureMask_complete]

/-- If every continuation has true-outcome mass at most `B`, binding any PMF to those
continuations also has true-outcome mass at most `B`. -/
theorem bind_success_le {A : Type*} (p : PMF A) (next : A → PMF Bool)
    (B : ℝ≥0∞) (h : ∀ a, next a true ≤ B) : (p.bind next) true ≤ B := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' a, p a * B := ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) _)
    _ = B := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
