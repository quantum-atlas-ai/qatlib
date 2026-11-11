/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Order.Real

/-!
# Costs of adaptive histories

This module assigns stage widths to finite histories and defines `pathCost`, `meanCost`,
`worstCost`, and `envelopeCost` relative to a probability mass function. It proves the
inequalities between these costs and gives a two-stage example where summing stage maxima
strictly exceeds the worst realizable path cost. These quantities provide resource bookkeeping
for adaptive quantum algorithms in the computational setting of [NielsenChuang2010].

## Main statements

* `mean_le_worst`: expected cost is at most the worst possible path cost.
* `worst_le_envelope`: the sum of stage maxima bounds the worst path cost.
* `exclusive_costs`: a concrete strict inequality between worst and envelope costs.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
namespace Qatlib.Foundations.ResourceBounds.AdaptiveCosts

/-- The sum of stage widths along a specified history. -/
def pathCost {H : Type*} {S : ℕ} (width : Fin S → H → ℕ) (h : H) : ℕ := ∑ s, width s h

/-- The finite set of histories assigned nonzero mass by `law`. -/
noncomputable def possibleHistories {H : Type*} [Fintype H] (law : PMF H) : Finset H := by
  classical
  exact Finset.univ.filter (fun h => law h ≠ 0)

/-- The maximum path cost over histories of nonzero probability. -/
noncomputable def worstCost {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) : ℕ :=
  (possibleHistories law).sup (pathCost width)

/-- The sum over stages of the maximum width among histories of nonzero probability. -/
noncomputable def envelopeCost {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) : ℕ :=
  ∑ s, (possibleHistories law).sup (width s)

/-- The expected path cost under the finite probability mass function `law`. -/
noncomputable def meanCost {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) : ℝ :=
  ∑ h, (law h).toReal * (pathCost width h : ℝ)

/-- Every history of nonzero probability has path cost bounded by `worstCost`. -/
theorem path_le_worst {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) (h : H) (hh : law h ≠ 0) :
    pathCost width h ≤ worstCost law width := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ h,hh⟩)

/-- The maximum total path cost is bounded by the sum of the separate stage maxima. -/
theorem worst_le_envelope {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) : worstCost law width ≤ envelopeCost law width := by
  apply Finset.sup_le
  intro h hh
  exact Finset.sum_le_sum (fun s _ => Finset.le_sup hh)

/-- The real-valued masses of a probability mass function on a finite type sum to one. -/
theorem pmf_real_sum {H : Type*} [Fintype H] (law : PMF H) : ∑ h, (law h).toReal = 1 := by
  rw [← ENNReal.toReal_sum]
  · have hs : (∑ h, law h) = 1 := by simpa only [tsum_fintype] using law.tsum_coe
    rw [hs,ENNReal.toReal_one]
  · intro h _
    exact law.apply_ne_top h

/-- The expected path cost is bounded by the maximum cost over possible histories. -/
theorem mean_le_worst {H : Type*} [Fintype H] {S : ℕ}
    (law : PMF H) (width : Fin S → H → ℕ) : meanCost law width ≤ worstCost law width := by
  calc
    _ ≤ ∑ h, (law h).toReal * (worstCost law width : ℝ) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hh : law h = 0
      · simp [hh]
      · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (path_le_worst law width h hh))
          ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul,pmf_real_sum,one_mul]

/-- A two-stage width function assigning cost one hundred to exactly one stage for each Boolean
history. -/
def exclusiveWidth : Fin 2 → Bool → ℕ := fun s h => if (decide (s = 0)) = h then 100 else 0

/-- The uniform Bernoulli probability mass function on Boolean histories. -/
noncomputable def exclusiveLaw : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

/-- For the two exclusive stage costs, the worst path cost is one hundred while the sum of stage
maxima is two hundred. -/
theorem exclusive_costs : worstCost exclusiveLaw exclusiveWidth = 100 ∧ envelopeCost exclusiveLaw exclusiveWidth = 200 := by
  have hpossible : possibleHistories exclusiveLaw = Finset.univ := by
    classical
    ext h
    cases h <;> norm_num [possibleHistories,exclusiveLaw,PMF.bernoulli_apply,tsub_eq_zero_iff_le]
  norm_num [worstCost, envelopeCost, hpossible, pathCost, exclusiveWidth, Fin.sum_univ_two,
    Fintype.univ_bool, Finset.sup_insert, Finset.sup_singleton]

end Qatlib.Foundations.ResourceBounds.AdaptiveCosts
