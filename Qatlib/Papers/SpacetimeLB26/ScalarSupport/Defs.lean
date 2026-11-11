/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Scalar quantities for spacetime bounds

This module defines finite width sums, contraction products, binary entropy, binary relative
entropy, and budget-feasible allocations for [BhartiHaugTanggara2026]. It supplies the
product-to-exponential and Jensen estimates used to bound the maximal survival product.

## Main statements

* `prod_one_sub_le_exp_neg_sum`: A finite product of `1 - f s`, with each `f s` in `[0, 1]`, is
  at most the exponential of minus their sum.
* `jensen_rpow_sum`: For positive `p` and positive `S`, the sum of `p^(q s)` is at least `S`
  times `p` raised to the average of the exponents.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport

open scoped BigOperators
open Finset

/-- The sum of the supplied layer-envelope widths. -/
def layerEnvelopeSum {S : ℕ} (q : Fin S → ℝ) : ℝ := ∑ s, q s

/-- The sum of the layer widths along a supplied record. -/
def recordCost {S : ℕ} (q : Fin S → ℝ) : ℝ := ∑ s, q s

/-- The sum of the supplied expected layer widths. -/
def expectedWidthsSum {S : ℕ} (q : Fin S → ℝ) : ℝ := ∑ s, q s

/-- The product over layers of the factors `1 - κ^(2 * q s)`. -/
def contractionProduct {S : ℕ} (κ : ℝ) (q : Fin S → ℝ) : ℝ :=
  ∏ s, (1 - κ ^ (2 * q s))

/-- Binary entropy in bits, expressed using the real logarithm. -/
def h2 (x : ℝ) : ℝ := -(x * Real.log x + (1 - x) * Real.log (1 - x)) / Real.log 2

/-- Binary relative entropy with natural logarithms, comparing Bernoulli parameters `Δ` and `p`. -/
def binaryKL (Δ p : ℝ) : ℝ :=
  Δ * Real.log (Δ / p) + (1 - Δ) * Real.log ((1 - Δ) / (1 - p))

/-- The condition that `δ` lies strictly between zero and `1/2` and has binary entropy `1/2`. -/
def IsGilbertVarshamovRate (δ : ℝ) : Prop := h2 δ = 1 / 2 ∧ 0 < δ ∧ δ < 1 / 2

/-- The nonnegative part `max 0 (log x)` of the real logarithm. -/
def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

/-- The finite set of integer width allocations bounded by `m` in every layer and with total
width at most `C`. -/
def feasibleAllocs (S m : ℕ) (C : ℝ) : Finset (Fin S → Fin (m + 1)) :=
  Finset.univ.filter (fun n => (∑ s, ((n s : ℕ) : ℝ)) ≤ C)

/-- The largest product of layer survival factors over budget-feasible allocations, or zero if
there are none. -/
noncomputable def maxSurvivalProd (S m : ℕ) (C p : ℝ) : ℝ :=
  if h : (feasibleAllocs S m C).Nonempty then
    (feasibleAllocs S m C).sup' h (fun n => ∏ s, (1 - p ^ (((n s : ℕ) : ℝ))))
  else 0

/-- A nonnegative budget makes the feasible-allocation set nonempty. -/
theorem feasibleAllocs_nonempty {S m : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    (feasibleAllocs S m C).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp only [feasibleAllocs, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using hC

/-- A finite product of `1 - f s`, with each `f s` in `[0, 1]`, is at most the exponential of
minus their sum. -/
theorem prod_one_sub_le_exp_neg_sum {S : ℕ} {f : Fin S → ℝ}
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    (∏ s, (1 - f s)) ≤ Real.exp (-(∑ s, f s)) := by
  have hstep : ∏ s : Fin S, (1 - f s) ≤ ∏ s : Fin S, Real.exp (-(f s)) := by
    refine Finset.prod_le_prod₀ (fun s _ => by linarith [hf s]) (fun s _ => ?_)
    simpa using Real.one_sub_le_exp_neg (f s)
  calc ∏ s, (1 - f s)
      ≤ ∏ s : Fin S, Real.exp (-(f s)) := hstep
    _ = Real.exp (-(∑ s, f s)) := by
        rw [← Real.exp_sum]
        congr 1
        simp [Finset.sum_neg_distrib]

/-- For positive `p` and positive `S`, the sum of `p^(q s)` is at least `S` times `p` raised to
the average of the exponents. -/
theorem jensen_rpow_sum {S : ℕ} {p : ℝ} (hp : 0 < p) (hS : 0 < S) (q : Fin S → ℝ) :
    (S : ℝ) * p ^ ((∑ s, q s) / (S : ℝ)) ≤ ∑ s, p ^ (q s) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => p ^ x) := convexOn_rpow_left hp
  have hjensen : p ^ (∑ s : Fin S, (1 / (S : ℝ)) • q s)
      ≤ ∑ s : Fin S, (1 / (S : ℝ)) • p ^ (q s) := by
    refine hconv.map_sum_le (t := Finset.univ) (w := fun _ : Fin S => 1 / (S : ℝ))
      (p := q) ?_ ?_ ?_
    · intro i _
      positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hSpos]
    · intro i _
      exact Set.mem_univ _
  simp only [smul_eq_mul] at hjensen
  have hsum1 : (∑ s : Fin S, (1 / (S : ℝ)) * q s) = (∑ s, q s) / (S : ℝ) := by
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
  rw [hsum1] at hjensen
  rw [← Finset.mul_sum] at hjensen
  have hS1 : (S : ℝ) * (1 / (S : ℝ)) = 1 := by
    rw [one_div, mul_inv_cancel₀ (ne_of_gt hSpos)]
  have hmul := mul_le_mul_of_nonneg_left hjensen hSpos.le
  rw [← mul_assoc, hS1, one_mul] at hmul
  exact hmul

/-- For a nonnegative budget, the maximal survival product is the finite supremum over feasible
allocations. -/
theorem maxSurvivalProd_eq {S m : ℕ} {C p : ℝ} (hC : 0 ≤ C) :
    maxSurvivalProd S m C p =
      (feasibleAllocs S m C).sup' (feasibleAllocs_nonempty (S := S) (m := m) hC)
        (fun n => ∏ s, (1 - p ^ (((n s : ℕ) : ℝ)))) := by
  rw [maxSurvivalProd, dif_pos (feasibleAllocs_nonempty (S := S) (m := m) hC)]

end Qatlib.Papers.SpacetimeLB26.ScalarSupport
