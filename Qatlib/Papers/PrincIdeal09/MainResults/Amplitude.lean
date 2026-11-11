/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Phase alignment and Fourier amplitude bounds

A finite family of phases lying within π / 4 of a common center has a sum whose norm is at least
its cardinality times √2 / 2. Applying this estimate to the expression `qftProb` gives a lower
bound of p / (8q) when p and q are positive [Schmidt2009].

## Main statements

* `segment_sum_norm_ge`: Aligned phases give a linear lower bound on the norm of their
  exponential sum.
* `qftProb_ge`: The squared-amplitude expression is bounded below by p / (8q).

## References

* [Schmidt, 2009][Schmidt2009]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PrincIdeal09.MainResults

/-- If `|x| ≤ π / 4`, then `cos x ≥ sqrt 2 / 2`. -/
theorem cos_ge_cos_pi_div_four {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ Real.cos x := by
  rw [← Real.cos_pi_div_four]
  have hxabs : Real.cos x = Real.cos |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cos_neg]
  rw [hxabs]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) ?_ ?_
  · linarith [Real.pi_pos]
  · exact hx

/-- When every phase lies within `π / 4` of `c`, the real part of the centered exponential sum
is at least `p * sqrt 2 / 2`. -/
theorem segment_sum_re_ge {p : ℕ} (φ : Fin p → ℝ) {c : ℝ}
    (hc : ∀ i, |φ i - c| ≤ Real.pi / 4) :
    (p : ℝ) * (Real.sqrt 2 / 2) ≤
      (∑ i, Complex.exp (((φ i - c : ℝ) : ℂ) * Complex.I)).re := by
  have hre :
      (∑ i, Complex.exp (((φ i - c : ℝ) : ℂ) * Complex.I)).re =
        ∑ i, Real.cos (φ i - c) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Complex.exp_ofReal_mul_I_re]
  rw [hre]
  calc (p : ℝ) * (Real.sqrt 2 / 2) = ∑ _i : Fin p, (Real.sqrt 2 / 2) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i, Real.cos (φ i - c) := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact cos_ge_cos_pi_div_four (hc i)

/-- When every phase lies within `π / 4` of `c`, the norm of their exponential sum is at least
`p * sqrt 2 / 2`. -/
theorem segment_sum_norm_ge {p : ℕ} (φ : Fin p → ℝ) {c : ℝ}
    (hc : ∀ i, |φ i - c| ≤ Real.pi / 4) :
    (p : ℝ) * (Real.sqrt 2 / 2) ≤
      ‖∑ i, Complex.exp (((φ i : ℝ) : ℂ) * Complex.I)‖ := by
  set S : ℂ := ∑ i, Complex.exp (((φ i : ℝ) : ℂ) * Complex.I) with hS
  have hfactor :
      S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I) =
        ∑ i, Complex.exp (((φ i - c : ℝ) : ℂ) * Complex.I) := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hre := segment_sum_re_ge φ hc
  have hrewrite :
      (S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)).re =
        (∑ i, Complex.exp (((φ i - c : ℝ) : ℂ) * Complex.I)).re := by
    rw [hfactor]
  have hre2 :
      (p : ℝ) * (Real.sqrt 2 / 2) ≤
        (S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)).re := by
    rw [hrewrite]
    exact hre
  have hnorm : ‖S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)‖ = ‖S‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hle :
      RCLike.re (S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) ≤
        ‖S * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)‖ :=
    RCLike.re_le_norm _
  rw [hnorm] at hle
  exact le_trans hre2 hle

/-- The squared norm of the phase sum divided by `4 * p * q`. -/
def qftProb (p : ℕ) (q : ℝ) (φ : Fin p → ℝ) : ℝ :=
  ‖∑ i, Complex.exp (((φ i : ℝ) : ℂ) * Complex.I)‖ ^ 2 / (4 * (p : ℝ) * q)

/-- For positive `p` and `q`, phases within `π / 4` of a common center give `qftProb p q φ ≥ p /
(8 * q)` [Schmidt2009]. -/
theorem qftProb_ge {p : ℕ} {q : ℝ} (hp : 0 < p) (hq : 0 < q) (φ : Fin p → ℝ)
    {c : ℝ} (hc : ∀ i, |φ i - c| ≤ Real.pi / 4) :
    (p : ℝ) / (8 * q) ≤ qftProb p q φ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnorm := segment_sum_norm_ge φ hc
  have hbase_nonneg : (0 : ℝ) ≤ (p : ℝ) * (Real.sqrt 2 / 2) := by positivity
  have hsq : ((p : ℝ) * (Real.sqrt 2 / 2)) ^ 2 ≤
      ‖∑ i, Complex.exp (((φ i : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    exact pow_le_pow_left₀ hbase_nonneg hnorm 2
  have hsqrt_sq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpsum : ((p : ℝ) * (Real.sqrt 2 / 2)) ^ 2 = (p : ℝ) ^ 2 / 2 := by
    rw [mul_pow, hsqrt_sq]; ring
  have hden : (0 : ℝ) < 4 * (p : ℝ) * q := by positivity
  unfold qftProb
  rw [le_div_iff₀ hden]
  rw [hpsum] at hsq

  have hrw : (p : ℝ) / (8 * q) * (4 * (p : ℝ) * q) = (p : ℝ) ^ 2 / 2 := by
    field_simp
    ring
  rw [hrw]
  exact hsq

end Qatlib.Papers.PrincIdeal09.MainResults
