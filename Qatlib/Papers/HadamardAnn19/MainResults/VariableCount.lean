/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Hadamard Search Variable Counts

This module studies the square-search variable count used in the body of [SuksmonoMinato2019].
`mainVars` counts the matrix entries and `ancillaVars` counts one ancillary coordinate for each
row and increasing column pair, giving the exact total `totalVars M = M ^ 2 * (M + 1) / 2`.

The real-valued count is asymptotically bounded by a cubic and has no quadratic big-O bound. The
order-four specialization gives 16 main variables and 24 ancillary variables.

## Main statements

* `two_mul_totalVars` and `totalVars_eq_closed_form` establish the exact count.
* `quadratic_lt_totalVars` gives an explicit size beyond which any fixed natural multiple of the
  quadratic is exceeded.
* `totalVars_isBigO_cubic` and `totalVars_not_isBigO_quadratic` establish the asymptotic bounds.
* `totalVars_four` computes the 40-variable order-four case.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

namespace Qatlib.Papers.HadamardAnn19.MainResults.VariableCount

set_option autoImplicit false

/-- The count `M ^ 2` of main Boolean coordinates for an order-`M` square sign matrix. -/
def mainVars (M : ℕ) : ℕ := M ^ 2

/-- The count `M * (M * (M - 1) / 2)` of ancillary coordinates, one per row and increasing
column pair, used in [SuksmonoMinato2019]. -/
def ancillaVars (M : ℕ) : ℕ := M * (M * (M - 1) / 2)

/-- The sum of the main and ancillary variable counts for the square Hadamard search. -/
def totalVars (M : ℕ) : ℕ := mainVars M + ancillaVars M

/-- Twice the total variable count is exactly `M ^ 2 * (M + 1)` for every natural order `M`. -/
theorem two_mul_totalVars (M : ℕ) : 2 * totalVars M = M ^ 2 * (M + 1) := by
  rcases M with _ | k
  · simp [totalVars, mainVars, ancillaVars]
  · unfold totalVars mainVars ancillaVars
    simp only [Nat.add_sub_cancel]
    have hk : 2 * ((k + 1) * k / 2) = (k + 1) * k :=
      Nat.two_mul_div_two_of_even (by simpa using Nat.even_mul_pred_self (k + 1))
    have hdouble :
        2 * ((k + 1) ^ 2 + (k + 1) * ((k + 1) * k / 2)) =
          (k + 1) ^ 2 * (k + 1 + 1) := by
      calc 2 * ((k + 1) ^ 2 + (k + 1) * ((k + 1) * k / 2))
          = 2 * (k + 1) ^ 2 + (k + 1) * (2 * ((k + 1) * k / 2)) := by ring
        _ = 2 * (k + 1) ^ 2 + (k + 1) * ((k + 1) * k) := by rw [hk]
        _ = (k + 1) ^ 2 * (k + 1 + 1) := by ring
    exact hdouble

/-- The total variable count equals the natural-number expression `M ^ 2 * (M + 1) / 2`. -/
theorem totalVars_eq_closed_form (M : ℕ) : totalVars M = M ^ 2 * (M + 1) / 2 := by
  apply Nat.eq_div_of_mul_eq_right two_ne_zero
  exact two_mul_totalVars M

/-- If `M ≥ 2 * C + 2`, the total variable count strictly exceeds `C * M ^ 2`. -/
theorem quadratic_lt_totalVars {C M : ℕ} (hM : 2 * C + 2 ≤ M) :
    C * M ^ 2 < totalVars M := by
  have hpos : 0 < M ^ 2 := pow_pos (by omega) 2
  have hlt : 2 * C * M ^ 2 < (M + 1) * M ^ 2 :=
    Nat.mul_lt_mul_of_pos_right (by omega) hpos
  have h2 := two_mul_totalVars M
  have hmid : 2 * (C * M ^ 2) < 2 * totalVars M := by
    rw [h2]
    calc 2 * (C * M ^ 2) = 2 * C * M ^ 2 := by ring
      _ < (M + 1) * M ^ 2 := hlt
      _ = M ^ 2 * (M + 1) := by ring
  omega

/-- The real-valued total variable count is `O(M³)` as the natural order tends to infinity,
formalizing the cubic upper bound in [SuksmonoMinato2019]. -/
theorem totalVars_isBigO_cubic :
    (fun M : ℕ => (totalVars M : ℝ)) =O[Filter.atTop] (fun M : ℕ => (M : ℝ) ^ 3) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  have hle : totalVars M ≤ M ^ 3 := by
    have h2 := two_mul_totalVars M
    have hM1 : M + 1 ≤ 2 * M := by omega
    have hK : M ^ 2 * (M + 1) ≤ 2 * M ^ 3 := by
      calc M ^ 2 * (M + 1) ≤ M ^ 2 * (2 * M) := Nat.mul_le_mul_left _ hM1
        _ = 2 * M ^ 3 := by ring
    omega
  have hR : (totalVars M : ℝ) ≤ (M : ℝ) ^ 3 := by exact_mod_cast hle
  rw [Real.norm_natCast, norm_pow, Real.norm_natCast]
  linarith

/-- The real-valued total variable count is not `O(M²)` as the natural order tends to infinity. -/
theorem totalVars_not_isBigO_quadratic :
    ¬ (fun M : ℕ => (totalVars M : ℝ)) =O[Filter.atTop]
        (fun M : ℕ => (M : ℝ) ^ 2) := by
  intro hO
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨c, hc⟩ := hO
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hc
  obtain ⟨C, hC⟩ := exists_nat_gt c
  set M : ℕ := N + 2 * C + 2 with hMdef
  have hMN : N ≤ M := by omega
  have hbig := hN M hMN
  rw [Real.norm_natCast, norm_pow, Real.norm_natCast] at hbig
  have hquad : (C : ℝ) * (M : ℝ) ^ 2 < (totalVars M : ℝ) := by
    have hnat : C * M ^ 2 < totalVars M := quadratic_lt_totalVars (by omega)
    exact_mod_cast hnat
  nlinarith [hbig, hquad, hC, sq_nonneg (M : ℝ)]

/-- For every natural coefficient `C`, some order has total variable count strictly greater than
`C * M ^ 2`. -/
theorem totalVars_exceeds_any_quadratic (C : ℕ) :
    ∃ M : ℕ, C * M ^ 2 < totalVars M :=
  ⟨2 * C + 2, quadratic_lt_totalVars (by omega)⟩

/-- Order four uses 16 main coordinates and 24 ancillary coordinates, giving 40 variables in
total. -/
theorem totalVars_four : mainVars 4 = 16 ∧ ancillaVars 4 = 24 ∧ totalVars 4 = 40 := by
  decide

end Qatlib.Papers.HadamardAnn19.MainResults.VariableCount
