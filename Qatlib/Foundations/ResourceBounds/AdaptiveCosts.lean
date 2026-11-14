/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

public import Qatlib.Foundations.ProbabilityCore.CoinLaw

@[expose] public section

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
noncomputable def exclusiveLaw : PMF Bool := Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli (1/2) (by norm_num)

/-- For the two exclusive stage costs, the worst path cost is one hundred while the sum of stage
maxima is two hundred. -/
theorem exclusive_costs : worstCost exclusiveLaw exclusiveWidth = 100 ∧ envelopeCost exclusiveLaw exclusiveWidth = 200 := by
  have hpossible : possibleHistories exclusiveLaw = Finset.univ := by
    classical
    ext h
    cases h <;> norm_num [possibleHistories,exclusiveLaw,Qatlib.Foundations.ProbabilityCore.CoinLaw.bernoulli_apply,tsub_eq_zero_iff_le]
  norm_num [worstCost, envelopeCost, hpossible, pathCost, exclusiveWidth, Fin.sum_univ_two,
    Fintype.univ_bool, Finset.sup_insert, Finset.sup_singleton]

end Qatlib.Foundations.ResourceBounds.AdaptiveCosts
