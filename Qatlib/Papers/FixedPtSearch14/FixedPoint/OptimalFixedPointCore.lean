/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointDefs
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.AmplitudeAmplification

/-!
# Analytic bounds for fixed-point search

This module develops the Chebyshev and hyperbolic-function estimates underlying the fixed-point
search construction of [YoderLowChuang2014]. It proves width identities, a common successful
length, access-count bounds, polynomial suppression bounds, and the response composition
identity.

It also establishes normalization and unitarity for the two-level word and formulates the two
recurrence bridges used by `ylc_master_response_of_bridges`. Explicit examples with phase π/3
and endpoint lemmas supplement these interfaces.

## Main statements

* `unifiedChoice`: a positive odd length with a uniform response bound.
* `accessCountOBound`: a universal logarithmic access-count estimate.
* `chebyshev_suppression_optimal`: the maximal polynomial suppression interval.
* `nestedResponseIdentity`: response composition under multiplication of lengths.
* `ylc_master_response_of_bridges`: the response formula from the two bridges.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix
open Polynomial
open Polynomial.Chebyshev

/-- Unfolds `cheb` as evaluation of the first-kind Chebyshev polynomial. -/
theorem cheb_eq (n : ℕ) (x : ℝ) : cheb n x = (T ℝ (n : ℤ)).eval x := rfl

/-- The degree-one Chebyshev polynomial evaluates to its argument. -/
theorem cheb_one (x : ℝ) : cheb 1 x = x := by
  simp [cheb_eq, T_one]

/-- If `0 < delta < 1`, then `1 < 1 / delta`. -/
theorem one_lt_one_div_of_lt {delta : ℝ} (hd : 0 < delta) (hd' : delta < 1) :
    1 < 1 / delta := by
  have h := one_div_lt_one_div_of_lt hd hd'
  rwa [one_div_one] at h

/-- If `0 < delta ≤ 1`, then `1 ≤ 1 / delta`. -/
theorem one_le_one_div_of_le {delta : ℝ} (hd : 0 < delta) (hd' : delta ≤ 1) :
    1 ≤ 1 / delta := by
  have h := one_div_le_one_div_of_le hd hd'
  rwa [one_div_one] at h

/-- A Chebyshev polynomial of odd degree vanishes at zero. -/
theorem cheb_zero_of_odd {n : ℕ} (hn : Odd n) : cheb n 0 = 0 := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  have h := T_eval_zero_of_odd (R := ℝ) (n := (n : ℤ)) hn'
  simpa [cheb_eq] using h

/-- Negating the argument of a Chebyshev polynomial multiplies its value by the sign determined
by the degree. -/
theorem cheb_T_eval_neg (n : ℕ) (x : ℝ) :
    cheb n (-x) = ((n : ℤ).negOnePow : ℝ) * cheb n x := by
  have h := T_eval_neg (R := ℝ) (n := (n : ℤ)) x
  simpa [cheb_eq] using h

/-- The square of the real coercion of the integer sign `negOnePow` is one. -/
theorem negOnePow_sq (n : ℕ) : (((n : ℤ).negOnePow : ℝ)) ^ 2 = 1 := by
  have h : (((n : ℤ).negOnePow : ℝ)) = (-1 : ℝ) ^ (n : ℤ).natAbs :=
    Int.coe_negOnePow ℝ _
  rw [h, ← pow_mul]
  have h2 : (n : ℤ).natAbs * 2 = 2 * (n : ℤ).natAbs := by ring
  rw [h2, pow_mul, neg_one_sq, one_pow]

/-- The squared Chebyshev value is invariant under negating its argument. -/
theorem cheb_sq_neg (n : ℕ) (x : ℝ) : cheb n (-x) ^ 2 = cheb n x ^ 2 := by
  rw [cheb_T_eval_neg, mul_pow, negOnePow_sq, one_mul]

/-- Replacing an argument by its absolute value leaves the squared Chebyshev value unchanged. -/
theorem cheb_abs_sq (n : ℕ) (x : ℝ) : cheb n (|x|) ^ 2 = cheb n x ^ 2 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, cheb_sq_neg]

/-- Composition of Chebyshev polynomials multiplies their degrees. -/
theorem cheb_comp (m n : ℕ) (x : ℝ) : cheb m (cheb n x) = cheb (m * n) x := by
  have h := T_mul (R := ℝ) (m : ℤ) (n : ℤ)
  have hcast : ((m * n : ℕ) : ℤ) = (m : ℤ) * (n : ℤ) := by norm_cast
  simp only [cheb_eq, hcast]
  rw [h, eval_comp]

/-- A Chebyshev polynomial has absolute value at most one on `[-1, 1]`. -/
theorem cheb_le_one {n : ℕ} {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) : |cheb n y| ≤ 1 := by
  have hy' : y = Real.cos (Real.arccos y) := by
    rw [Real.cos_arccos hy.1 hy.2]
  rw [hy', cheb_eq, T_real_cos]
  exact Real.abs_cos_le_one _

/-- Evaluating `cheb n` at `cosh t` gives `cosh (n * t)`. -/
theorem cheb_one_div_cosh {n : ℕ} (t : ℝ) :
    cheb n (Real.cosh t) = Real.cosh ((n : ℝ) * t) := by
  have h := T_real_cosh (n := (n : ℤ)) t
  simpa [cheb_eq] using h

/-- A Chebyshev polynomial has value at least one at every argument at least one. -/
theorem cheb_one_le_of_one_le {L : ℕ} {y : ℝ} (hy : 1 ≤ y) : 1 ≤ cheb L y := by
  conv_rhs => rw [show y = Real.cosh (Real.arcosh y) by rw [Real.cosh_arcosh hy]]
  rw [cheb_one_div_cosh]
  exact Real.one_le_cosh _

/-- For positive degree, the Chebyshev evaluation function is strictly increasing on `[1, ∞)`. -/
theorem cheb_strictMonoOn_one_le (L : ℕ) (hL : 1 ≤ L) :
    StrictMonoOn (cheb L) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hx0 : 0 ≤ Real.arcosh x := Real.arcosh_nonneg hx1
  have hy0 : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy1
  have hlt : Real.arcosh x < Real.arcosh y :=
    (Real.arcosh_lt_arcosh (by exact lt_of_lt_of_le (by norm_num) hx1)
      (by exact lt_of_lt_of_le (by norm_num) hy1)).mpr hxy
  have hmul : ((L : ℝ) * Real.arcosh x) < ((L : ℝ) * Real.arcosh y) := by
    have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
    exact mul_lt_mul_of_pos_left hlt hLp
  have hx' : cheb L x = Real.cosh ((L : ℝ) * Real.arcosh x) := by
    conv_lhs => rw [show x = Real.cosh (Real.arcosh x) by rw [Real.cosh_arcosh hx1]]
    rw [cheb_one_div_cosh]
  have hy' : cheb L y = Real.cosh ((L : ℝ) * Real.arcosh y) := by
    conv_lhs => rw [show y = Real.cosh (Real.arcosh y) by rw [Real.cosh_arcosh hy1]]
    rw [cheb_one_div_cosh]
  rw [hx', hy']
  refine (Real.cosh_lt_cosh).mpr ?_
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hx0),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hy0)]
  exact hmul

/-- The width parameter is positive for positive length and `0 < delta < 1`. -/
theorem ylcGamma_pos {L : ℕ} {delta : ℝ} (hL : 0 < L) (hd : 0 < delta) (hd' : delta < 1) :
    0 < ylcGamma L delta := by
  have hcos : 0 < Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) := Real.cosh_pos _
  rw [ylcGamma]
  exact one_div_pos.mpr hcos

/-- The width parameter is less than one for positive length and `0 < delta < 1`. -/
theorem ylcGamma_lt_one {L : ℕ} {delta : ℝ} (hL : 0 < L) (hd : 0 < delta) (hd' : delta < 1) :
    ylcGamma L delta < 1 := by
  have h1 : 1 < 1 / delta := one_lt_one_div_of_lt hd hd'
  have harg : 0 < Real.arcosh (1 / delta) / (L : ℝ) :=
    div_pos (Real.arcosh_pos h1) (by exact_mod_cast hL)
  have hcos : 1 < Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) :=
    Real.one_lt_cosh.mpr harg.ne'
  rw [ylcGamma, div_lt_one (lt_trans (by norm_num) hcos)]
  linarith

/-- For positive length and `0 < delta < 1`, evaluating `cheb L` at the reciprocal width gives
`1 / delta`. -/
theorem cheb_one_div_gamma {L : ℕ} {delta : ℝ} (hL : 0 < L) (hd : 0 < delta)
    (hd' : delta < 1) : cheb L (1 / ylcGamma L delta) = 1 / delta := by
  have hcos : 0 < Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) := Real.cosh_pos _
  have hγ : 1 / ylcGamma L delta = Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) := by
    rw [ylcGamma, one_div_one_div]
  have h1 : 1 ≤ 1 / delta := one_le_one_div_of_le hd (le_of_lt hd')
  rw [hγ, cheb_one_div_cosh]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hL
  rw [mul_div_cancel₀ _ hL0, Real.cosh_arcosh h1]

/-- For positive length and `0 < delta < 1`, increasing the length by one does not decrease the
width. -/
theorem ylcGamma_mono_le {L : ℕ} {delta : ℝ} (hL : 0 < L) (hd : 0 < delta) (hd' : delta < 1) :
    ylcGamma L delta ≤ ylcGamma (L + 1) delta := by
  have h1 : 1 < 1 / delta := one_lt_one_div_of_lt hd hd'
  have hA : 0 < Real.arcosh (1 / delta) := Real.arcosh_pos h1
  set A := Real.arcosh (1 / delta)
  have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
  have hLp1 : 0 < ((L + 1 : ℕ) : ℝ) := by
    have : (0:ℕ) < L + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hstep : A / ((L + 1 : ℕ) : ℝ) < A / (L : ℝ) := by
    have hLL : (L : ℝ) < ((L + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact div_lt_div_of_pos_left hA hLp hLL
  have hcos : Real.cosh (A / ((L + 1 : ℕ) : ℝ)) < Real.cosh (A / (L : ℝ)) := by
    refine (Real.cosh_lt_cosh).mpr ?_
    rw [abs_of_nonneg (div_nonneg (le_of_lt hA) (le_of_lt hLp1)),
      abs_of_nonneg (div_nonneg (le_of_lt hA) (le_of_lt hLp))]
    exact hstep
  have hpos : 0 < Real.cosh (A / ((L + 1 : ℕ) : ℝ)) := Real.cosh_pos _
  have hpos' : 0 < Real.cosh (A / (L : ℝ)) := Real.cosh_pos _
  rw [ylcGamma, ylcGamma]
  exact one_div_le_one_div_of_le hpos (le_of_lt hcos)

/-- For positive length and `0 < delta < 1`, the displayed hyperbolic cosine is the reciprocal
of `ylcGamma L delta`. -/
theorem one_div_ylcGamma_cosh {L : ℕ} {delta : ℝ} (hL : 0 < L) (hd : 0 < delta)
    (hd' : delta < 1) :
    Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) = 1 / ylcGamma L delta := by
  rw [ylcGamma, one_div_one_div]

/-- For positive lengths and `0 < delta < 1`, nesting width parameters multiplies the lengths. -/
theorem ylcGamma_nested {L1 L2 : ℕ} {delta : ℝ} (h1 : 1 ≤ L1) (h2 : 1 ≤ L2)
    (hd : 0 < delta) (hd' : delta < 1) :
    ylcGamma L1 (ylcGamma L2 delta) = ylcGamma (L1 * L2) delta := by
  have hL1p : 0 < L1 := lt_of_lt_of_le (by norm_num) h1
  have hL2p : 0 < L2 := lt_of_lt_of_le (by norm_num) h2
  have hd1pos : 0 < ylcGamma L2 delta := ylcGamma_pos hL2p hd hd'
  have hd1lt : ylcGamma L2 delta < 1 := ylcGamma_lt_one hL2p hd hd'
  have hApos : 0 ≤ Real.arcosh (1 / delta) := Real.arcosh_nonneg
    (one_le_one_div_of_le hd (le_of_lt hd'))
  have h1d : Real.arcosh (1 / ylcGamma L2 delta) =
      Real.arcosh (1 / delta) / (L2 : ℝ) := by
    rw [(one_div_ylcGamma_cosh hL2p hd hd').symm,
      Real.arcosh_cosh (div_nonneg hApos (Nat.cast_nonneg _))]
  have hL1ne : (L1:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hL1p
  have hL2ne : (L2:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hL2p
  have hstep : Real.arcosh (1 / ylcGamma L2 delta) / (L1 : ℝ) =
      Real.arcosh (1 / delta) / ((L2 : ℝ) * (L1 : ℝ)) := by
    rw [h1d, div_div]
  have hcast : ((L2 : ℝ) * (L1 : ℝ)) = (((L2 * L1 : ℕ) : ℝ)) :=
    (Nat.cast_mul L2 L1).symm
  have hcomm : (L2 * L1 : ℕ) = L1 * L2 := by ring
  rw [ylcGamma, hstep, hcast, hcomm, ylcGamma]

/-- For nonnegative `u`, `sinh u ≤ u * cosh u`. -/
theorem sinh_le_mul_cosh {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ≤ u * Real.cosh u := by
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
      (y * Real.sinh y) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => z * Real.cosh z)
        (1 * Real.cosh y + y * Real.sinh y) y := by
      convert (hasDerivAt_id' y).mul (Real.hasDerivAt_cosh y) using 1 <;>
        first | rfl | (funext z; rfl) | ring
    have h2 : HasDerivAt (fun z : ℝ => Real.sinh z) (Real.cosh y) y :=
      Real.hasDerivAt_sinh y
    convert h1.sub h2 using 1 <;>
      first | rfl | (funext z; rfl) | ring
  have hmono : Monotone (fun z : ℝ => z * Real.cosh z - Real.sinh z) :=
    monotone_of_hasDerivAt_nonneg hd (fun x => by
      rcases le_or_gt 0 x with hx | hx
      · exact mul_nonneg hx (Real.sinh_nonneg_iff.mpr hx)
      · have h2 : Real.sinh x ≤ 0 :=
          le_of_not_gt fun h => absurd ((Real.sinh_pos_iff).mp h) (not_lt.mpr (le_of_lt hx))
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hx) h2)
  have h0 : (0:ℝ) * Real.cosh 0 - Real.sinh 0 = 0 := by simp
  have hge := hmono hu
  linarith

/-- For nonnegative `u`, `(1 - u ^ 2 / 2) * cosh u ≤ 1`. -/
theorem cosh_mul_one_sub_half_sq_le_one {u : ℝ} (hu : 0 ≤ u) :
    (1 - u ^ 2 / 2) * Real.cosh u ≤ 1 := by
  have hdf : ∀ y : ℝ, HasDerivAt (fun w : ℝ => (1 - w ^ 2 / 2) * Real.cosh w)
      ((1 - y ^ 2 / 2) * Real.sinh y - y * Real.cosh y) y := by
    intro y
    have h1a : HasDerivAt (fun w : ℝ => w ^ 2 / 2) y y := by
      convert (hasDerivAt_id' y).pow 2 |>.div_const 2 using 1 <;>
        first | rfl | (funext z; rfl) | ring
    have h1 : HasDerivAt (fun w : ℝ => 1 - w ^ 2 / 2) (-(y)) y := by
      convert (hasDerivAt_const y (1:ℝ)).sub h1a using 1 <;>
        first | rfl | (funext z; rfl) | ring
    have h2 : HasDerivAt (fun w : ℝ => Real.cosh w) (Real.sinh y) y :=
      Real.hasDerivAt_cosh y
    convert h1.mul h2 using 1 <;>
      first | rfl | (funext z; rfl) | ring
  have hanti : AntitoneOn (fun w : ℝ => (1 - w ^ 2 / 2) * Real.cosh w) (Set.Ici (0:ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici _)
      (fun x _ => (hdf x).continuousAt.continuousWithinAt)
      (fun x _ => (hdf x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
        have hd' : deriv (fun w : ℝ => (1 - w ^ 2 / 2) * Real.cosh w) x
            = (1 - x ^ 2 / 2) * Real.sinh x - x * Real.cosh x := (hdf x).deriv
        rw [hd']
        by_cases h : x ^ 2 ≤ 2
        · have hle : 0 ≤ 1 - x ^ 2 / 2 := by nlinarith
          have hle' : 1 - x ^ 2 / 2 ≤ 1 := by nlinarith
          have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
          have h1 : (1 - x ^ 2 / 2) * Real.sinh x ≤ 1 * Real.sinh x :=
            mul_le_mul_of_nonneg_right hle' hs
          have h2 : Real.sinh x ≤ x * Real.cosh x := sinh_le_mul_cosh hx0
          have h3 : (1 - x ^ 2 / 2) * Real.sinh x ≤ x * Real.cosh x := by linarith
          linarith
        · have hle : 1 - x ^ 2 / 2 ≤ 0 := by nlinarith
          have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
          have h1 : (1 - x ^ 2 / 2) * Real.sinh x ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hle hs
          have h2 : 0 ≤ x * Real.cosh x := mul_nonneg hx0 (le_of_lt (Real.cosh_pos x))
          linarith)
  have hH : (1 - u ^ 2 / 2) * Real.cosh u ≤ (1 - (0:ℝ) ^ 2 / 2) * Real.cosh 0 :=
    hanti (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0)) (Set.mem_Ici.mpr hu) hu
  have hH0 : (1 - (0:ℝ) ^ 2 / 2) * Real.cosh 0 = 1 := by norm_num
  rw [hH0] at hH
  exact hH

/-- For `0 ≤ u < 1`, `cosh u ≤ 1 / √(1 - u ^ 2)`. -/
theorem cosh_le_one_div_sqrt_one_sub_sq {u : ℝ} (hu : 0 ≤ u) (hu' : u < 1) :
    Real.cosh u ≤ 1 / Real.sqrt (1 - u ^ 2) := by
  have hsq : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hhalf : 0 < 1 - u ^ 2 / 2 := by nlinarith
  have hH : (1 - u ^ 2 / 2) * Real.cosh u ≤ 1 := cosh_mul_one_sub_half_sq_le_one hu
  have h1 : Real.cosh u ≤ 1 / (1 - u ^ 2 / 2) := by
    rw [le_div_iff₀ hhalf]
    nlinarith
  have h2 : 1 / (1 - u ^ 2 / 2) ≤ 1 / Real.sqrt (1 - u ^ 2) := by
    have hs : Real.sqrt (1 - u ^ 2) ≤ 1 - u ^ 2 / 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith
      · nlinarith
    have hsp : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    exact one_div_le_one_div_of_le hsp hs
  exact le_trans h1 h2

/-- For `0 < x < 1`, `√x ≤ arcosh (1 / √(1 - x))`. -/
theorem sqrt_le_arcosh_one_div_sqrt {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    Real.sqrt x ≤ Real.arcosh (1 / Real.sqrt (1 - x)) := by
  have hu0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hu1 : Real.sqrt x < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (le_of_lt hx) (by linarith)
  have husq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hle : Real.cosh (Real.sqrt x) ≤ 1 / Real.sqrt (1 - (Real.sqrt x) ^ 2) :=
    cosh_le_one_div_sqrt_one_sub_sq (le_of_lt hu0) hu1
  have hrewrite : Real.sqrt (1 - (Real.sqrt x) ^ 2) = Real.sqrt (1 - x) := by
    rw [husq]
  have h1 : 1 ≤ 1 / Real.sqrt (1 - x) := by
    have hs : Real.sqrt (1 - x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have hs0 : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr (by linarith)
    exact one_le_one_div_of_le hs0 hs
  have hcos_le : Real.cosh (Real.sqrt x) ≤ 1 / Real.sqrt (1 - x) := by
    rw [← hrewrite]
    exact hle
  have hx2 : Real.sqrt x = Real.arcosh (Real.cosh (Real.sqrt x)) := by
    rw [Real.arcosh_cosh (le_of_lt hu0)]
  rw [hx2]
  refine (Real.arcosh_le_arcosh (Real.cosh_pos _) (by positivity)).mpr hcos_le

/-- For `0 < delta < 1`, `arcosh (1 / delta) ≤ log (2 / delta)`. -/
theorem arcosh_inv_delta_le_log {delta : ℝ} (hd : 0 < delta) (hd' : delta < 1) :
    Real.arcosh (1 / delta) ≤ Real.log (2 / delta) := by
  have h1 : 1 ≤ 1 / delta := one_le_one_div_of_le hd (le_of_lt hd')
  have hs : Real.sqrt (1 / delta ^ 2 - 1) ≤ 1 / delta := by
    have h : 1 / delta ^ 2 - 1 ≤ 1 / delta ^ 2 := by
      have := sq_pos_of_ne_zero hd.ne'
      nlinarith
    have hp : 0 ≤ 1 / delta := le_of_lt (one_div_pos.mpr hd)
    have harg : 0 ≤ 1 / delta ^ 2 - 1 := by
      have h2pos : 0 < delta ^ 2 := sq_pos_of_ne_zero hd.ne'
      have h2le : delta ^ 2 ≤ 1 := by nlinarith
      have hdiv := one_div_le_one_div_of_le h2pos h2le
      rw [one_div_one] at hdiv
      linarith
    rw [Real.sqrt_le_iff]
    constructor
    · exact hp
    · have : (1 / delta) ^ 2 = 1 / delta ^ 2 := by ring
      rw [this]
      exact h
  have hsum : 0 < 1 / delta + Real.sqrt (1 / delta ^ 2 - 1) := by
    positivity
  have h2 : 1 / delta + Real.sqrt (1 / delta ^ 2 - 1) ≤ 2 / delta := by
    have h2e : (2:ℝ) / delta = 2 * (1 / delta) := by ring
    rw [h2e]
    linarith
  have hlog : Real.log (1 / delta + Real.sqrt (1 / delta ^ 2 - 1)) ≤ Real.log (2 / delta) :=
    Real.log_le_log hsum h2
  have hdef : Real.arcosh (1 / delta) =
      Real.log (1 / delta + Real.sqrt (1 / delta ^ 2 - 1)) := by
    rw [Real.arcosh]
    have h : (1 / delta) ^ 2 - 1 = 1 / delta ^ 2 - 1 := by ring
    rw [h]
  rw [hdef]
  exact hlog

/-- Unfolds the Chebyshev expression defining `responseProb`. -/
theorem responseProb_eq (L : ℕ) (delta lam : ℝ) :
    responseProb L delta lam =
      1 - (delta * cheb L (Real.sqrt (1 - lam) / ylcGamma L delta)) ^ 2 := rfl

/-- When `lam0 ≠ 1`, the chosen length is twice the ceiling of the displayed
inverse-hyperbolic-cosine ratio, plus one. -/
theorem ylcLength_eq (lam0 delta : ℝ) (h : lam0 ≠ 1) :
    ylcLength lam0 delta =
      2 * Nat.ceil (Real.arcosh (1 / delta) /
        Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1 := by
  rw [ylcLength, if_neg h]

/-- For unit lower bound on the good mass, the chosen length is one. -/
theorem ylcLength_one (delta : ℝ) : ylcLength 1 delta = 1 := by
  rw [ylcLength, if_pos rfl]

/-- For `0 < lam0 < 1`, the chosen length is odd. -/
theorem ylcLength_odd {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    Odd (ylcLength lam0 delta) := by
  rw [ylcLength_eq _ _ (ne_of_lt hl0')]
  exact ⟨Nat.ceil (Real.arcosh (1 / delta) /
    Real.arcosh (1 / Real.sqrt (1 - lam0))), by omega⟩

/-- For `0 < lam0 < 1`, the chosen length is at least one. -/
theorem ylcLength_one_le {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    1 ≤ ylcLength lam0 delta := by
  rw [ylcLength_eq _ _ (ne_of_lt hl0')]
  exact Nat.le_add_left _ _

/-- For `0 < lam0 < 1`, `arcosh (1 / √(1 - lam0))` is positive. -/
private theorem arcosh_bound_pos {lam0 : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    0 < Real.arcosh (1 / Real.sqrt (1 - lam0)) := by
  have h : 1 < 1 / Real.sqrt (1 - lam0) := by
    have hs : 0 < Real.sqrt (1 - lam0) := Real.sqrt_pos.mpr (by linarith)
    have hs1 : Real.sqrt (1 - lam0) < 1 := by
      have h : Real.sqrt (1 - lam0) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      rwa [Real.sqrt_one] at h
    exact one_lt_one_div_of_lt hs hs1
  exact Real.arcosh_pos h

/-- For `0 < delta < 1`, `arcosh (1 / delta)` is nonnegative. -/
private theorem arcosh_delta_nonneg {delta : ℝ} (hd : 0 < delta) (hd' : delta < 1) :
    0 ≤ Real.arcosh (1 / delta) :=
  Real.arcosh_nonneg (one_le_one_div_of_le hd (le_of_lt hd'))

/-- For `lam0` and `delta` in `(0, 1)`, the chosen length makes `arcosh (1 / delta)` divided by
that length at most `arcosh (1 / √(1 - lam0))`. -/
theorem ylcLength_meets_bound {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1)
    (hd : 0 < delta) (hd' : delta < 1) :
    Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℝ)) ≤
      Real.arcosh (1 / Real.sqrt (1 - lam0)) := by
  have hBpos := arcosh_bound_pos hl0 hl0'
  have hA := arcosh_delta_nonneg hd hd'
  have hLpos : 0 < ((ylcLength lam0 delta : ℕ) : ℝ) := by
    have h1 := ylcLength_one_le (lam0 := lam0) (delta := delta) hl0 hl0'
    have : (0:ℕ) < ylcLength lam0 delta := by omega
    exact_mod_cast this
  have hLce : ((ylcLength lam0 delta : ℕ) : ℝ) =
      2 * (Nat.ceil (Real.arcosh (1 / delta) /
        Real.arcosh (1 / Real.sqrt (1 - lam0))) : ℝ) + 1 := by
    rw [ylcLength_eq _ _ (ne_of_lt hl0')]
    push_cast
    rfl
  set c := Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) with hc
  have hceil : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil _
  have hLc : c < ((ylcLength lam0 delta : ℕ) : ℝ) := by
    rw [hLce]
    have : (c:ℝ) ≤ 2 * (Nat.ceil c : ℝ) + 1 := by
      have := hceil
      have h2 : 0 ≤ 2 * (Nat.ceil c : ℝ) := by positivity
      linarith
    linarith
  have hAc : Real.arcosh (1 / delta) =
      c * Real.arcosh (1 / Real.sqrt (1 - lam0)) := by
    rw [hc, div_mul_cancel₀ _ (ne_of_gt hBpos)]
  have hmain : Real.arcosh (1 / delta) ≤
      ((ylcLength lam0 delta : ℕ) : ℝ) * Real.arcosh (1 / Real.sqrt (1 - lam0)) := by
    rw [hAc]
    exact mul_le_mul_of_nonneg_right (le_of_lt hLc) (le_of_lt hBpos)
  rw [div_le_iff₀ hLpos, mul_comm]
  exact hmain

/-- For `lam0` and `delta` in `(0, 1)`, the chosen length gives Chebyshev response at least `1 -
delta ^ 2` for every `lam ∈ [lam0, 1]` [YoderLowChuang2014]. -/
theorem responseProb_succ_le {lam0 delta lam : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1)
    (hd : 0 < delta) (hd' : delta < 1) (hlam : lam0 ≤ lam) (hlam' : lam ≤ 1) :
    1 - delta ^ 2 ≤ responseProb (ylcLength lam0 delta) delta lam := by
  have hmeets := ylcLength_meets_bound hl0 hl0' hd hd'
  have hLpos : 0 < (ylcLength lam0 delta : ℕ) :=
    lt_of_lt_of_le (by norm_num)
      (ylcLength_one_le (lam0 := lam0) (delta := delta) hl0 hl0')
  have harg : 0 ≤ Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℕ) : ℝ) :=
    div_nonneg (arcosh_delta_nonneg hd hd') (Nat.cast_nonneg _)
  have hs0 : 0 < Real.sqrt (1 - lam0) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - lam0) < 1 := by
    have h : Real.sqrt (1 - lam0) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    rwa [Real.sqrt_one] at h
  have hB1 : 1 ≤ 1 / Real.sqrt (1 - lam0) :=
    one_le_one_div_of_le hs0 (le_of_lt hs1)
  have hB0 : 0 ≤ Real.arcosh (1 / Real.sqrt (1 - lam0)) :=
    Real.arcosh_nonneg hB1
  have hcos_le : Real.cosh (Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℕ) : ℝ)) ≤
      Real.cosh (Real.arcosh (1 / Real.sqrt (1 - lam0))) :=
    (Real.cosh_le_cosh).mpr (by
      rw [abs_of_nonneg harg, abs_of_nonneg hB0]
      exact hmeets)
  have hBcos : Real.cosh (Real.arcosh (1 / Real.sqrt (1 - lam0))) =
      1 / Real.sqrt (1 - lam0) := Real.cosh_arcosh hB1
  have hcospos : 0 < Real.cosh (Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℕ) : ℝ)) :=
    Real.cosh_pos _
  have hγ : Real.sqrt (1 - lam0) ≤ ylcGamma (ylcLength lam0 delta) delta := by
    rw [ylcGamma, le_one_div hs0 hcospos, ← hBcos]
    exact hcos_le
  have hnum : Real.sqrt (1 - lam) ≤ Real.sqrt (1 - lam0) := by
    refine Real.sqrt_le_sqrt ?_
    linarith
  have hγpos : 0 < ylcGamma (ylcLength lam0 delta) delta :=
    ylcGamma_pos hLpos hd hd'
  have hy : Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta ∈ Set.Icc (-1:ℝ) 1 := by
    have hle : Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta ≤ 1 := by
      rw [div_le_one hγpos]
      exact le_trans hnum hγ
    have hge : -1 ≤ Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta := by
      have hnn : 0 ≤ Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta :=
        div_nonneg (Real.sqrt_nonneg _) (le_of_lt hγpos)
      linarith
    exact ⟨hge, hle⟩
  have hcheb : |cheb (ylcLength lam0 delta)
      (Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta)| ≤ 1 := cheb_le_one hy
  rw [responseProb_eq]
  have hsq : (delta * cheb (ylcLength lam0 delta)
      (Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta)) ^ 2 ≤ delta ^ 2 := by
    have h := abs_le.mp hcheb
    set c := cheb (ylcLength lam0 delta)
      (Real.sqrt (1 - lam) / ylcGamma (ylcLength lam0 delta) delta)
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
    have hmul : (delta * c) ^ 2 = delta ^ 2 * c ^ 2 := by ring
    rw [hmul]
    have hle := mul_le_mul_of_nonneg_left hc2 (sq_nonneg delta)
    rw [mul_one] at hle
    linarith
  linarith

/-- For positive odd length and `0 < delta < 1`, the Chebyshev response at zero good mass is
zero. -/
theorem responseProb_zero {L : ℕ} {delta : ℝ} (hL : Odd L) (hL' : 1 ≤ L)
    (hd : 0 < delta) (hd' : delta < 1) : responseProb L delta 0 = 0 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL'
  have h : cheb L (1 / ylcGamma L delta) = 1 / delta := cheb_one_div_gamma hL0 hd hd'
  rw [responseProb_eq]
  have hsqrt : Real.sqrt (1 - (0:ℝ)) / ylcGamma L delta = 1 / ylcGamma L delta := by
    rw [sub_zero, Real.sqrt_one]
  rw [hsqrt, h]
  have hdd : delta * (1 / delta) = 1 := mul_one_div_cancel hd.ne'
  rw [hdd, one_pow, sub_self]

/-- For positive odd length and `0 < delta < 1`, the Chebyshev response at unit good mass is
one. -/
theorem responseProb_one {L : ℕ} {delta : ℝ} (hL : Odd L) (hL' : 1 ≤ L)
    (hd : 0 < delta) (hd' : delta < 1) : responseProb L delta 1 = 1 := by
  rw [responseProb_eq]
  have hsqrt : Real.sqrt (1 - (1:ℝ)) = 0 := by rw [sub_self, Real.sqrt_zero]
  rw [hsqrt, zero_div, cheb_zero_of_odd hL, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    sub_zero]

/-- For `0 < delta < 1`, the length-one response is one for every `lam ≥ 1`. -/
theorem responseProb_one_of_one_le (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    ∀ lam, 1 ≤ lam → responseProb 1 delta lam = 1 := by
  intro lam hlam
  have hsqrt : Real.sqrt (1 - lam) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  rw [responseProb_eq, hsqrt, zero_div, cheb_one, mul_zero,
    zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero]

/-- A word with `l` iterates has query count `2 * l`. -/
theorem wordQueryCount_eq (l : ℕ) : wordQueryCount l = 2 * l := rfl

/-- A word with `l` iterates has preparation-access count `2 * l`. -/
theorem wordPreparationCount_eq (l : ℕ) : wordPreparationCount l = 2 * l := rfl

/-- Concatenating `l` lists of length two gives a list of length `2 * l`. -/
private theorem flatMap_constTwo_length (l : ℕ) (f : ℕ → List ℝ) (hf : ∀ i, (f i).length = 2) :
    ((List.range l).flatMap f).length = 2 * l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have h2 : (List.flatMap f [l]).length = 2 := by
      simp [hf]
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, h2]
    ring

/-- The displayed analytic phase list contains `2 * l` angles. -/
theorem wordPhaseList_length (l L : ℕ) (g : ℝ) :
    ((List.range l).flatMap fun i =>
      [ylcAlpha L (i + 1) g, -(ylcAlpha L (l - i) g)]).length = 2 * l := by
  refine flatMap_constTwo_length l _ (fun i => ?_)
  simp

/-- For a positive bit count `b`, every real angle has an integer multiple of `2 * π / 2 ^ b`
within `π / 2 ^ b`. -/
theorem exists_dyadic_phase (b : ℕ) (hb : 0 < b) (theta : ℝ) :
    ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b := by
  have hTpos : 0 < (2:ℝ) ^ b := by positivity
  have h2pi : 0 < 2 * Real.pi := by
    have := Real.pi_pos
    positivity
  set x := theta * (2:ℝ) ^ b / (2 * Real.pi) with hx
  obtain ⟨q, hq⟩ : ∃ q : ℤ, |x - (q:ℝ)| ≤ 1 / 2 := by
    by_cases h : x - ⌊x⌋ ≤ 1 / 2
    · refine ⟨⌊x⌋, ?_⟩
      have h1 : (0:ℝ) ≤ x - ⌊x⌋ := by
        have := Int.floor_le x
        linarith
      have h2 : x - (⌊x⌋:ℝ) = |x - (⌊x⌋:ℝ)| := (abs_of_nonneg h1).symm
      rw [← h2]
      exact h
    · refine ⟨⌊x⌋ + 1, ?_⟩
      have hgt : (1/2:ℝ) < x - ⌊x⌋ := lt_of_not_ge h
      have h1 : (x:ℝ) < ⌊x⌋ + 1 := Int.lt_floor_add_one x
      have h3 : |x - (((⌊x⌋ + 1 : ℤ) : ℝ))| = (((⌊x⌋ + 1 : ℤ) : ℝ)) - x := by
        rw [abs_sub_comm]
        have h1' : (0:ℝ) ≤ (((⌊x⌋ + 1 : ℤ) : ℝ)) - x := by
          push_cast
          linarith
        exact abs_of_nonneg h1'
      rw [h3]
      push_cast
      linarith
  refine ⟨q, ?_⟩
  have hkey : theta - (2 * Real.pi * (q:ℝ)) / (2:ℝ) ^ b =
      (2 * Real.pi / (2:ℝ) ^ b) * (x - (q:ℝ)) := by
    rw [hx]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (div_pos h2pi hTpos)]
  have hhalf : (2 * Real.pi / (2:ℝ) ^ b) * (1 / 2) = Real.pi / (2:ℝ) ^ b := by
    field_simp
  calc (2 * Real.pi / (2:ℝ) ^ b) * |x - (q:ℝ)| ≤
      (2 * Real.pi / (2:ℝ) ^ b) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hq (le_of_lt (div_pos h2pi hTpos))
    _ = Real.pi / (2:ℝ) ^ b := hhalf

/-- For `L ≥ 1` and `0 < delta < 1`, a real polynomial of degree at most `L`, normalized at one
and bounded by `delta` on `[-a, a]` with `a > 0`, satisfies `a ≤ ylcGamma L delta`
[YoderLowChuang2014]. -/
theorem chebyshev_suppression_optimal {L : ℕ} {delta : ℝ} {q : ℝ[X]} {a : ℝ}
    (hL : 1 ≤ L) (hd : 0 < delta) (hd' : delta < 1) (hqdeg : q.degree ≤ (L : ℕ))
    (hq1 : q.eval 1 = 1) (ha : 0 < a) (hbound : ∀ y ∈ Set.Icc (-a) a, |q.eval y| ≤ delta) :
    a ≤ ylcGamma L delta := by
  have ha1 : a < 1 := by
    by_contra hc
    have hc' : 1 ≤ a := not_lt.mp hc
    have h1mem : (1:ℝ) ∈ Set.Icc (-a) a := ⟨by linarith, by linarith⟩
    have := hbound 1 h1mem
    rw [hq1, abs_one] at this
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hinv1 : 1 ≤ 1 / a := one_le_one_div_of_le ha (le_of_lt ha1)
  set P : ℝ[X] := C delta⁻¹ * q.comp (C a * X) with hPdef
  have hPeval : ∀ x : ℝ, P.eval x = delta⁻¹ * q.eval (a * x) := by
    intro x
    rw [hPdef, eval_mul, eval_C, eval_comp, eval_C_mul, eval_X]
  have hPdeg : P.degree ≤ (L : ℕ) := by
    have hPnd : P.natDegree ≤ L := by
      rw [hPdef, Polynomial.natDegree_C_mul (inv_ne_zero hd.ne')]
      have h1 : (q.comp (C a * X)).natDegree ≤ q.natDegree * (C a * X).natDegree :=
        Polynomial.natDegree_comp_le
      have h2 : (C a * X).natDegree ≤ 1 :=
        Polynomial.natDegree_le_of_degree_le (Polynomial.degree_C_mul_X_le a)
      refine le_trans h1 (le_trans (Nat.mul_le_mul_left _ h2) ?_)
      rw [Nat.mul_one]
      exact Polynomial.natDegree_le_of_degree_le hqdeg
    exact le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hPnd)
  have hPbnd : ∀ x ∈ Set.Icc (-1:ℝ) 1, |P.eval x| ≤ 1 := by
    intro x hx
    rw [hPeval]
    have hx' : |x| ≤ 1 := abs_le.mpr hx
    have hax : a * x ∈ Set.Icc (-a) a := by
      have h1 : a * x ≤ a := by
        have := mul_le_mul_of_nonneg_left hx.2 (le_of_lt ha)
        nlinarith
      have h2 : -a ≤ a * x := by
        have := mul_le_mul_of_nonneg_left hx.1 (le_of_lt ha)
        nlinarith
      exact ⟨h2, h1⟩
    have hqa : |q.eval (a * x)| ≤ delta := hbound (a * x) hax
    have hmul : |delta⁻¹ * q.eval (a * x)| = delta⁻¹ * |q.eval (a * x)| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hd)]
    rw [hmul]
    have hle : delta⁻¹ * |q.eval (a * x)| ≤ delta⁻¹ * delta :=
      mul_le_mul_of_nonneg_left hqa (le_of_lt (inv_pos.mpr hd))
    have hdd : delta⁻¹ * delta = 1 := inv_mul_cancel₀ hd.ne'
    linarith
  have hle : P.eval (1 / a) ≤ (T ℝ L).eval (1 / a) := by
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := L) (P := P) (k := 0) (x := 1 / a) hinv1 hPdeg hPbnd
    simpa [Function.iterate_zero_apply] using h
  have hPe : P.eval (1 / a) = 1 / delta := by
    rw [hPeval, mul_one_div_cancel ha.ne', hq1, mul_one, one_div]
  have hT : (T ℝ L).eval (1 / a) = cheb L (1 / a) := rfl
  rw [hT, hPe] at hle
  have hγ : cheb L (1 / ylcGamma L delta) = 1 / delta :=
    cheb_one_div_gamma hLpos hd hd'
  have hγ1 : 1 ≤ 1 / ylcGamma L delta :=
    one_le_one_div_of_le (ylcGamma_pos hLpos hd hd') (le_of_lt (ylcGamma_lt_one hLpos hd hd'))
  have hmono := cheb_strictMonoOn_one_le L hL
  have hcomp : cheb L (1 / ylcGamma L delta) ≤ cheb L (1 / a) := by
    rw [hγ]
    exact hle
  have hle' : (1 / ylcGamma L delta) ≤ (1 / a) :=
    (hmono.le_iff_le (Set.mem_Ici.mpr hγ1) (Set.mem_Ici.mpr hinv1)).mp hcomp
  exact le_of_one_div_le_one_div (ylcGamma_pos hLpos hd hd') hle'

/-- For `L ≥ 1` and `lam0, delta ∈ (0, 1)`, a real polynomial of degree at most `L`, normalized
at one and bounded by `delta` on the displayed interval, satisfies the stated
inverse-hyperbolic-cosine degree bound [YoderLowChuang2014]. -/
theorem chebyshev_degree_lower_bound {L : ℕ} {lam0 delta : ℝ} {q : ℝ[X]}
    (hL : 1 ≤ L) (hl0 : 0 < lam0) (hl0' : lam0 < 1) (hd : 0 < delta) (hd' : delta < 1)
    (hqdeg : q.degree ≤ (L : ℕ)) (hq1 : q.eval 1 = 1)
    (hbound : ∀ y ∈ Set.Icc (-Real.sqrt (1 - lam0)) (Real.sqrt (1 - lam0)),
      |q.eval y| ≤ delta) :
    Real.arcosh (1 / delta) / (L : ℝ) ≤ Real.arcosh (1 / Real.sqrt (1 - lam0)) := by
  have hs : 0 < Real.sqrt (1 - lam0) := Real.sqrt_pos.mpr (by linarith)
  have hγ := chebyshev_suppression_optimal hL hd hd' hqdeg hq1 hs hbound
  have hs1 : Real.sqrt (1 - lam0) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hB1 : 1 ≤ 1 / Real.sqrt (1 - lam0) := one_le_one_div_of_le hs hs1
  have hcospos : 0 < Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) := Real.cosh_pos _
  have hstep : Real.cosh (Real.arcosh (1 / delta) / (L : ℝ)) ≤ 1 / Real.sqrt (1 - lam0) := by
    rw [ylcGamma] at hγ
    rw [le_one_div hs hcospos] at hγ
    exact hγ
  have hBcos : Real.cosh (Real.arcosh (1 / Real.sqrt (1 - lam0))) =
      1 / Real.sqrt (1 - lam0) := Real.cosh_arcosh hB1
  have harg : 0 ≤ Real.arcosh (1 / delta) / (L : ℝ) :=
    div_nonneg (arcosh_delta_nonneg hd hd') (Nat.cast_nonneg _)
  have hB0 : 0 ≤ Real.arcosh (1 / Real.sqrt (1 - lam0)) := Real.arcosh_nonneg hB1
  rw [← hBcos] at hstep
  have habs := (Real.cosh_le_cosh).mp hstep
  rw [abs_of_nonneg harg, abs_of_nonneg hB0] at habs
  exact habs

/-- A positive universal constant bounds the chosen iterate, preparation, and query counts by `C
* log (2 / delta) / √lam0` for `lam0, delta ∈ (0, 1)`. For `delta ≤ 1 / 2`, it also gives
the displayed comparison with `log (1 / delta)` [YoderLowChuang2014]. -/
theorem accessCountOBound :
    ∃ C : ℝ, 0 < C ∧
    ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      let L := ylcLength lam0 delta
      let l := (L - 1) / 2
      let bound := C * Real.log (2 / delta) / Real.sqrt lam0
      (l : ℝ) ≤ bound ∧
        (wordPreparationCount l : ℝ) ≤ bound ∧
        (wordQueryCount l : ℝ) ≤ bound ∧
        (delta ≤ 1 / 2 → Real.log (2 / delta) ≤ 2 * Real.log (1 / delta)) := by
  refine ⟨6, by norm_num, ?_⟩
  intro lam0 delta hl0 hl0' hd hd'
  have hL : ylcLength lam0 delta = 2 * Nat.ceil (Real.arcosh (1 / delta) /
      Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1 := ylcLength_eq _ _ (ne_of_lt hl0')
  have hcpos := arcosh_bound_pos hl0 hl0'
  have hApos := arcosh_delta_nonneg hd hd'
  have hs : 0 < Real.sqrt lam0 := Real.sqrt_pos.mpr hl0
  have hlogpos : 0 < Real.log (2 / delta) := by
    have h1 : 1 < 2 / delta := by
      have h := one_lt_one_div_of_lt hd hd'
      have h2 : (2:ℝ) / delta = 2 * (1 / delta) := by ring
      rw [h2]
      linarith
    exact Real.log_pos h1
  have hcle : Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) ≤
      Real.log (2 / delta) / Real.sqrt lam0 := by
    have hstep1 : Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) ≤
        Real.log (2 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) :=
      div_le_div_of_nonneg_right (arcosh_inv_delta_le_log hd hd') (le_of_lt hcpos)
    have hstep2 : Real.log (2 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) ≤
        Real.log (2 / delta) / Real.sqrt lam0 := by
      have hden : Real.sqrt lam0 ≤ Real.arcosh (1 / Real.sqrt (1 - lam0)) :=
        sqrt_le_arcosh_one_div_sqrt hl0 hl0'
      exact div_le_div_of_nonneg_left (le_of_lt hlogpos) hs hden
    exact le_trans hstep1 hstep2
  have hceil : ((Nat.ceil (Real.arcosh (1 / delta) /
        Real.arcosh (1 / Real.sqrt (1 - lam0))) : ℕ) : ℝ) ≤
      Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) + 1 := by
    set c := Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0)) with hc
    rcases Nat.eq_zero_or_pos ⌈c⌉₊ with h | h
    · rw [h]
      have hc0 : 0 ≤ c := div_nonneg hApos (le_of_lt hcpos)
      simp
      linarith
    · have h1 : (⌈c⌉₊ - 1 : ℕ) < ⌈c⌉₊ := Nat.sub_lt h zero_lt_one
      have hlt : ((⌈c⌉₊ - 1 : ℕ) : ℝ) < c :=
        (Nat.lt_ceil (n := ⌈c⌉₊ - 1) (a := c)).mp h1
      have hcast : ((⌈c⌉₊ : ℕ) : ℝ) = ((⌈c⌉₊ - 1 : ℕ) : ℝ) + 1 := by
        have h2 : ⌈c⌉₊ = (⌈c⌉₊ - 1) + 1 := by omega
        exact_mod_cast h2
      rw [hcast]
      linarith
  have hl_eq : ((ylcLength lam0 delta - 1) / 2 : ℕ) =
      Nat.ceil (Real.arcosh (1 / delta) / Real.arcosh (1 / Real.sqrt (1 - lam0))) := by
    rw [hL]
    omega
  have hB0 : 1 / 2 ≤ Real.log (2 / delta) / Real.sqrt lam0 := by
    have hs1 : Real.sqrt lam0 ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt hl0')
    have h1 : (0.5:ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    have h2 : Real.log 2 ≤ Real.log (2 / delta) := by
      refine Real.log_le_log (by norm_num) ?_
      have h := le_of_lt (one_lt_one_div_of_lt hd hd')
      have h2e : (2:ℝ) / delta = 2 * (1 / delta) := by ring
      rw [h2e]
      nlinarith
    rw [le_div_iff₀ hs]
    nlinarith
  have hx : (0:ℝ) ≤ Real.log (2 / delta) / Real.sqrt lam0 :=
    div_nonneg (le_of_lt hlogpos) (le_of_lt hs)
  have hconv : (6:ℝ) * Real.log (2 / delta) / Real.sqrt lam0 =
      6 * (Real.log (2 / delta) / Real.sqrt lam0) := by ring
  have hcl : (((ylcLength lam0 delta - 1) / 2 : ℕ) : ℝ) ≤
      3 * (Real.log (2 / delta) / Real.sqrt lam0) := by
    rw [hl_eq]
    have h1 : ((Nat.ceil (Real.arcosh (1 / delta) /
          Real.arcosh (1 / Real.sqrt (1 - lam0))) : ℕ) : ℝ) ≤
        Real.log (2 / delta) / Real.sqrt lam0 + 1 :=
      by linarith [hceil, hcle]
    have h2 : 1 ≤ 2 * (Real.log (2 / delta) / Real.sqrt lam0) := by
      linarith [hB0]
    linarith
  have hmain : (((ylcLength lam0 delta - 1) / 2 : ℕ) : ℝ) ≤
      6 * Real.log (2 / delta) / Real.sqrt lam0 := by
    rw [hconv]
    linarith [hcl, hx]
  have hprep : (wordPreparationCount ((ylcLength lam0 delta - 1) / 2) : ℝ) ≤
      6 * Real.log (2 / delta) / Real.sqrt lam0 := by
    rw [wordPreparationCount_eq]
    push_cast
    rw [hconv]
    linarith [hcl, hx]
  have hquery : (wordQueryCount ((ylcLength lam0 delta - 1) / 2) : ℝ) ≤
      6 * Real.log (2 / delta) / Real.sqrt lam0 := by
    rw [wordQueryCount_eq]
    push_cast
    rw [hconv]
    linarith [hcl, hx]
  have hbridge : delta ≤ 1 / 2 → Real.log (2 / delta) ≤ 2 * Real.log (1 / delta) := by
    intro hdelt
    have h1 : Real.log (2 / delta) = Real.log 2 + Real.log (1 / delta) := by
      have h2e : (2:ℝ) / delta = 2 * (1 / delta) := by ring
      rw [h2e, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (one_div_ne_zero (ne_of_gt hd))]
    have h2 : Real.log 2 ≤ Real.log (1 / delta) := by
      refine Real.log_le_log (by norm_num) ?_
      rw [le_one_div (by norm_num : (0:ℝ) < 2) hd]
      linarith
    linarith
  exact ⟨hmain, hprep, hquery, hbridge⟩

/-- The preparation count is `l + l`, the query count is `2 * l`, and the query count plus one
is `2 * l + 1`. -/
theorem paidLedgerCompleteness :
    ∀ l : ℕ,
    wordPreparationCount l = l + l ∧ wordQueryCount l = 2 * l ∧
      wordQueryCount l + 1 = 2 * l + 1 := by
  intro l
  refine ⟨?_, rfl, rfl⟩
  rw [wordPreparationCount_eq, two_mul]

/-- For `0 < delta < 1`, the analytic phase list for `l` iterates contains exactly `2 * l`
angles. -/
theorem phaseAngleCount :
    ∀ (l : ℕ) (delta : ℝ), 0 < delta → delta < 1 →
    let L := 2 * l + 1
    let g := ylcGamma L delta
    ((List.range l).flatMap fun i =>
      [ylcAlpha L (i + 1) g, -(ylcAlpha L (l - i) g)]).length = 2 * l := by
  intro l delta _ _
  exact wordPhaseList_length l (2 * l + 1) (ylcGamma (2 * l + 1) delta)

/-- For positive `b`, every phase angle can be approximated by a dyadic multiple of `2 * π` with
error at most `π / 2 ^ b`. -/
theorem phaseCompilationInterface :
    ∀ (b : ℕ) (theta : ℝ), 0 < b →
    ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b :=
  fun b theta hb => exists_dyadic_phase b hb theta

/-- For positive length and `0 < delta < 1`, a degree-bounded real polynomial normalized at one
cannot be bounded by `delta` on a positive symmetric interval wider than `ylcGamma L delta`
[YoderLowChuang2014]. -/
theorem chebyshevOptimalSuppression :
    ∀ (L : ℕ) (delta : ℝ) (q : ℝ[X]) (a : ℝ),
    1 ≤ L → 0 < delta → delta < 1 → q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
      0 < a → (∀ y ∈ Set.Icc (-a) a, |q.eval y| ≤ delta) → a ≤ ylcGamma L delta :=
  fun L delta q a hL hd hd' hqdeg hq1 ha hbound =>
    chebyshev_suppression_optimal hL hd hd' hqdeg hq1 ha hbound

/-- For the stated positive length and parameters in `(0, 1)`, uniform polynomial suppression on
the good-mass interval implies the displayed inverse-hyperbolic-cosine degree bound
[YoderLowChuang2014]. -/
theorem chebyshevDegreeLowerBound :
    ∀ (L : ℕ) (lam0 delta : ℝ) (q : ℝ[X]),
    1 ≤ L → 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
      (∀ y ∈ Set.Icc (-Real.sqrt (1 - lam0)) (Real.sqrt (1 - lam0)),
        |q.eval y| ≤ delta) →
        Real.arcosh (1 / delta) / (L : ℝ) ≤
          Real.arcosh (1 / Real.sqrt (1 - lam0)) :=
  fun L lam0 delta q hL hl0 hl0' hd hd' hqdeg hq1 hbound =>
    chebyshev_degree_lower_bound hL hl0 hl0' hd hd' hqdeg hq1 hbound

/-- For `lam0, delta ∈ (0, 1)`, the chosen common length satisfies the displayed
inverse-hyperbolic-cosine bound. -/
theorem unifiedLengthMeetsLowerBound :
    ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
    Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℝ)) ≤
      Real.arcosh (1 / Real.sqrt (1 - lam0)) :=
  fun lam0 delta hl0 hl0' hd hd' => ylcLength_meets_bound hl0 hl0' hd hd'

/-- For positive length and `0 < delta < 1`, the width parameter does not decrease when the
length increases by one. -/
theorem widthWidening :
    ∀ (L : ℕ) (delta : ℝ), 0 < L → 0 < delta → delta < 1 →
    ylcGamma L delta ≤ ylcGamma (L + 1) delta :=
  fun L delta hL hd hd' => ylcGamma_mono_le hL hd hd'

/-- Combines the universal access-count bound, exact ledgers, phase counts, and dyadic phase
approximation with Chebyshev suppression and degree bounds, the chosen-length inequality,
and width monotonicity [YoderLowChuang2014]. -/
theorem g2 :
    (∃ C : ℝ, 0 < C ∧
    ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      let L := ylcLength lam0 delta
      let l := (L - 1) / 2
      let bound := C * Real.log (2 / delta) / Real.sqrt lam0
      (l : ℝ) ≤ bound ∧
        (wordPreparationCount l : ℝ) ≤ bound ∧
        (wordQueryCount l : ℝ) ≤ bound ∧
        (delta ≤ 1 / 2 → Real.log (2 / delta) ≤ 2 * Real.log (1 / delta))) ∧
  (∀ l : ℕ,
    wordPreparationCount l = l + l ∧ wordQueryCount l = 2 * l ∧
      wordQueryCount l + 1 = 2 * l + 1) ∧
  (∀ (l : ℕ) (delta : ℝ), 0 < delta → delta < 1 →
    let L := 2 * l + 1
    let g := ylcGamma L delta
    ((List.range l).flatMap fun i =>
      [ylcAlpha L (i + 1) g, -(ylcAlpha L (l - i) g)]).length = 2 * l) ∧
  (∀ (b : ℕ) (theta : ℝ), 0 < b →
    ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b) ∧
  (∀ (L : ℕ) (delta : ℝ) (q : ℝ[X]) (a : ℝ),
    1 ≤ L → 0 < delta → delta < 1 → q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
      0 < a → (∀ y ∈ Set.Icc (-a) a, |q.eval y| ≤ delta) → a ≤ ylcGamma L delta) ∧
  (∀ (L : ℕ) (lam0 delta : ℝ) (q : ℝ[X]),
    1 ≤ L → 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
      (∀ y ∈ Set.Icc (-Real.sqrt (1 - lam0)) (Real.sqrt (1 - lam0)),
        |q.eval y| ≤ delta) →
        Real.arcosh (1 / delta) / (L : ℝ) ≤
          Real.arcosh (1 / Real.sqrt (1 - lam0))) ∧
  (∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
    Real.arcosh (1 / delta) / ((ylcLength lam0 delta : ℝ)) ≤
      Real.arcosh (1 / Real.sqrt (1 - lam0))) ∧
  (∀ (L : ℕ) (delta : ℝ), 0 < L → 0 < delta → delta < 1 →
    ylcGamma L delta ≤ ylcGamma (L + 1) delta) :=
  ⟨accessCountOBound, paidLedgerCompleteness, phaseAngleCount, phaseCompilationInterface,
    chebyshevOptimalSuppression, chebyshevDegreeLowerBound, unifiedLengthMeetsLowerBound,
    widthWidening⟩

/-- For positive length and `0 < delta < 1`, the width lies in `(0, 1)` and its reciprocal has
Chebyshev value `1 / delta`. -/
theorem widthIdentity :
    (∀ (L : ℕ) (delta : ℝ), 0 < L → 0 < delta ∧ delta < 1 →
      0 < ylcGamma L delta ∧ ylcGamma L delta < 1 ∧
        cheb L (1 / ylcGamma L delta) = 1 / delta) := by
  intro L delta hL hd
  exact ⟨ylcGamma_pos hL hd.1 hd.2, ylcGamma_lt_one hL hd.1 hd.2,
    cheb_one_div_gamma hL hd.1 hd.2⟩

/-- For `lam0, delta ∈ (0, 1)`, the chosen length is positive and odd and gives response at
least `1 - delta ^ 2` uniformly for `lam ∈ [lam0, 1]` [YoderLowChuang2014]. -/
theorem unifiedChoice :
    (∀ (lam0 delta : ℝ), 0 < lam0 ∧ lam0 < 1 → 0 < delta ∧ delta < 1 →
      Odd (ylcLength lam0 delta) ∧ 1 ≤ ylcLength lam0 delta ∧
        ∀ lam, lam0 ≤ lam ∧ lam ≤ 1 →
          1 - delta ^ 2 ≤ responseProb (ylcLength lam0 delta) delta lam) := by
  intro lam0 delta hl hd
  exact ⟨ylcLength_odd hl.1 hl.2, ylcLength_one_le hl.1 hl.2,
    fun lam hl' => responseProb_succ_le hl.1 hl.2 hd.1 hd.2 hl'.1 hl'.2⟩

/-- For `0 < delta < 1`, a unit good-mass lower bound selects length one, whose response is one
for every `lam ≥ 1`. -/
theorem trivialBoundCompletion :
    (∀ delta : ℝ, 0 < delta ∧ delta < 1 →
      ylcLength 1 delta = 1 ∧ ∀ lam, 1 ≤ lam → responseProb 1 delta lam = 1) := by
  intro delta hd
  exact ⟨ylcLength_one delta, responseProb_one_of_one_le delta hd.1 hd.2⟩

/-- For positive odd length and `0 < delta < 1`, the response equals zero at good mass zero and
one at good mass one. -/
theorem responseEndpoints :
    (∀ (L : ℕ) (delta : ℝ), Odd L → 1 ≤ L → 0 < delta ∧ delta < 1 →
      responseProb L delta 0 = 0 ∧ responseProb L delta 1 = 1) := by
  intro L delta hL hL' hd
  exact ⟨responseProb_zero hL hL' hd.1 hd.2, responseProb_one hL hL' hd.1 hd.2⟩

/-- The query and preparation counts both equal `2 * l`, and the query count plus one equals `2
* l + 1`. -/
theorem accessLedger :
    (∀ l : ℕ, wordQueryCount l = 2 * l ∧ wordPreparationCount l = 2 * l ∧
      wordQueryCount l + 1 = 2 * l + 1) := by
  intro l
  exact ⟨rfl, rfl, rfl⟩

/-- For normalized source and target with unit good mass and `0 < delta < 1`, the full-register
length-one success probability is one. -/
theorem degenerateAligned :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (s T : QState I) (delta : ℝ),
      Normalized s → Normalized T → 0 < delta ∧ delta < 1 →
        goodMass T s = 1 → fullSuccessProb s T 1 delta = 1) := by
  intro I _ _ s T delta _ _ _ hgood
  have hW : fullWordMatrix s (alignedTarget T s) 1 delta = 1 := by
    show ((List.range ((1 - 1) / 2)).map fun i =>
      -(fullStateReflection s (ylcAlpha 1 (i + 1) (ylcGamma 1 delta)) *
        fullTargetReflectionFull (alignedTarget T s)
          (-(ylcAlpha 1 (1 - 1 - i) (ylcGamma 1 delta))))).reverse.prod = 1
    simp
  show ‖Qatlib.Foundations.PureStateMath.Inner T
      (fullWordMatrix s (alignedTarget T s) 1 delta *ᵥ s)‖ ^ 2 = 1
  rw [hW, Matrix.one_mulVec]
  exact hgood

/-- A full source reflection multiplies its normalized defining state by `exp(-i * alpha)`. -/
theorem fullStateReflection_mulVec_self {I : Type} [Fintype I] [DecidableEq I]
    {s : QState I} (hs : Normalized s) (alpha : ℝ) :
    fullStateReflection s alpha *ᵥ s = (Complex.exp (-(Complex.I * alpha))) • s := by
  show (1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct s) *ᵥ s =
    Complex.exp (-(Complex.I * alpha)) • s
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, outerProduct_mulVec s s, inner_self_eq_one hs]
  rw [Matrix.one_mulVec, one_smul]
  have h : (s : QState I) - (1 - Complex.exp (-(Complex.I * alpha))) • s =
      (1 - (1 - Complex.exp (-(Complex.I * alpha)))) • s := by
    have h2 : (1:ℂ) • s - (1 - Complex.exp (-(Complex.I * alpha))) • s =
        (1 - (1 - Complex.exp (-(Complex.I * alpha)))) • s :=
      (sub_smul (1:ℂ) (1 - Complex.exp (-(Complex.I * alpha))) s).symm
    rw [one_smul] at h2
    exact h2
  rw [h, show (1:ℂ) - (1 - Complex.exp (-(Complex.I * alpha))) =
    Complex.exp (-(Complex.I * alpha)) by ring]

/-- Multiplying the second state by a complex scalar multiplies the inner product by that
scalar. -/
theorem inner_smul_right {I : Type} [Fintype I] [DecidableEq I]
    (psi phi : QState I) (c : ℂ) : Qatlib.Foundations.PureStateMath.Inner psi (c • phi) = c * Qatlib.Foundations.PureStateMath.Inner psi phi := by
  simp only [inner_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- If each matrix in a list sends a state to a scalar multiple of itself, their product also
sends that state to a scalar multiple of itself. -/
private theorem listProd_smul_self {I : Type} [Fintype I] [DecidableEq I]
    {s : QState I} {xs : List (Matrix I I ℂ)} (hxs : ∀ x ∈ xs, ∃ c : ℂ, x *ᵥ s = c • s) :
    ∃ c : ℂ, xs.prod *ᵥ s = c • s := by
  induction xs with
  | nil => exact ⟨1, by rw [List.prod_nil, Matrix.one_mulVec, one_smul]⟩
  | cons x xs ih =>
    obtain ⟨c1, hc1⟩ := hxs x (by simp)
    obtain ⟨c2, hc2⟩ := ih (fun y hy => hxs y (by simp [hy]))
    refine ⟨c1 * c2, ?_⟩
    rw [List.prod_cons, ← Matrix.mulVec_mulVec, hc2, Matrix.mulVec_smul, hc1, ← mul_smul,
      mul_comm c2 c1]

/-- For positive `L2` and `0 < delta < 1`, the inner width lies in `(0, 1)` and its reciprocal
is the displayed hyperbolic cosine. -/
theorem innerErrorParameter :
    (∀ (L2 : ℕ) (delta : ℝ), 1 ≤ L2 → 0 < delta → delta < 1 →
      0 < ylcGamma L2 delta ∧ ylcGamma L2 delta < 1 ∧
        Real.cosh (Real.arcosh (1 / delta) / (L2 : ℝ)) = 1 / ylcGamma L2 delta) := by
  intro L2 delta hL2 hd hd'
  have hL2p : 0 < L2 := lt_of_lt_of_le (by norm_num) hL2
  exact ⟨ylcGamma_pos hL2p hd hd', ylcGamma_lt_one hL2p hd hd',
    one_div_ylcGamma_cosh hL2p hd hd'⟩

/-- Composing Chebyshev evaluations of degrees `L1` and `L2` gives degree `L1 * L2`. -/
theorem chebyshevSemigroup :
    (∀ (L1 L2 : ℕ) (x : ℝ), cheb L2 (cheb L1 x) = cheb (L1 * L2) x) := by
  intro L1 L2 x
  rw [cheb_comp, Nat.mul_comm L2 L1]

/-- For positive lengths, `0 < delta < 1`, and `lam ∈ [0, 1]`, composing the responses with the
prescribed inner error parameter multiplies their lengths [YoderLowChuang2014]. -/
theorem nestedResponseIdentity :
    (∀ (L1 L2 : ℕ) (delta lam : ℝ), 1 ≤ L1 → 1 ≤ L2 → 0 < delta → delta < 1 →
      0 ≤ lam → lam ≤ 1 →
        responseProb L2 delta (responseProb L1 (ylcGamma L2 delta) lam) =
          responseProb (L1 * L2) delta lam) := by
  intro L1 L2 delta lam hL1 hL2 hd hd' _ _
  have hL2p : 0 < L2 := lt_of_lt_of_le (by norm_num) hL2
  have hd1p : 0 < ylcGamma L2 delta := ylcGamma_pos hL2p hd hd'
  have hpe : responseProb L1 (ylcGamma L2 delta) lam =
      1 - (ylcGamma L2 delta * cheb L1
        (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))) ^ 2 :=
    responseProb_eq L1 (ylcGamma L2 delta) lam
  have hsub : 1 - responseProb L1 (ylcGamma L2 delta) lam =
      (ylcGamma L2 delta * cheb L1
        (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))) ^ 2 := by
    rw [hpe]
    ring
  have hsqrt : Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) =
      |ylcGamma L2 delta * cheb L1
        (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))| := by
    rw [hsub, Real.sqrt_sq_eq_abs]
  have habs : |ylcGamma L2 delta * cheb L1
        (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))| =
      ylcGamma L2 delta * |cheb L1
        (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))| := by
    rw [abs_mul, abs_of_pos hd1p]
  have harg : Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta =
      |cheb L1 (Real.sqrt (1 - lam) / ylcGamma L1 (ylcGamma L2 delta))| := by
    rw [hsqrt, habs]
    exact mul_div_cancel_left₀ _ (ne_of_gt hd1p)
  have hcheb : (cheb L2
        (Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta)) ^ 2 =
      (cheb (L1 * L2) (Real.sqrt (1 - lam) / ylcGamma (L1 * L2) delta)) ^ 2 := by
    rw [harg, cheb_abs_sq, cheb_comp, ylcGamma_nested hL1 hL2 hd hd', Nat.mul_comm L2 L1]
  have hsq : (delta * cheb L2
        (Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta)) ^ 2 =
      (delta * cheb (L1 * L2) (Real.sqrt (1 - lam) / ylcGamma (L1 * L2) delta)) ^ 2 := by
    have h : delta ^ 2 * (cheb L2
          (Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta)) ^ 2 =
        delta ^ 2 * (cheb (L1 * L2)
          (Real.sqrt (1 - lam) / ylcGamma (L1 * L2) delta)) ^ 2 :=
      congrArg (fun z : ℝ => delta ^ 2 * z) hcheb
    have e1 : (delta * cheb L2
        (Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta)) ^ 2 =
        delta ^ 2 * (cheb L2
          (Real.sqrt (1 - responseProb L1 (ylcGamma L2 delta) lam) / ylcGamma L2 delta)) ^ 2 := by
      ring
    have e2 : (delta * cheb (L1 * L2) (Real.sqrt (1 - lam) / ylcGamma (L1 * L2) delta)) ^ 2 =
        delta ^ 2 * (cheb (L1 * L2)
          (Real.sqrt (1 - lam) / ylcGamma (L1 * L2) delta)) ^ 2 := by
      ring
    rw [e1, e2, h]
  rw [responseProb_eq L2 delta (responseProb L1 (ylcGamma L2 delta) lam),
    responseProb_eq (L1 * L2) delta lam, hsq]

/-- The nested odd length has iterate count `l1 + 2 * l1 * l2 + l2`, and its query count
satisfies the displayed nesting identity. -/
theorem nestedComplexity :
    (∀ l1 l2 : ℕ,
      (2 * l1 + 1) * (2 * l2 + 1) = 2 * (l1 + 2 * l1 * l2 + l2) + 1 ∧
        wordQueryCount (l1 + 2 * l1 * l2 + l2) =
          wordQueryCount l2 + (2 * l2 + 1) * wordQueryCount l1) := by
  intro l1 l2
  constructor
  · ring
  · simp only [wordQueryCount_eq]
    ring

/-- For normalized source and target, `0 < delta < 1`, and zero initial good mass, the
full-register word has zero success probability. -/
theorem zeroMassFails :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (s T : QState I) (L : ℕ) (delta : ℝ),
      Normalized s → Normalized T → 0 < delta → delta < 1 →
        goodMass T s = 0 → fullSuccessProb s T L delta = 0) := by
  intro I _ _ s T L delta hns _ hd hd' hmass
  have hmass' : ‖Qatlib.Foundations.PureStateMath.Inner T s‖ ^ 2 = 0 := hmass
  have hinner : Qatlib.Foundations.PureStateMath.Inner T s = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hmass')
  have halt : alignedTarget T s = 0 := by
    rw [alignedTarget, hinner, norm_zero, Complex.ofReal_zero, zero_div, zero_smul]
  have houter : outerProduct (0 : QState I) = 0 := by
    ext i j
    simp [outerProduct]
  have htref : ∀ beta : ℝ, fullTargetReflectionFull (alignedTarget T s) beta = 1 := by
    intro beta
    show (1 : Matrix I I ℂ) - (1 - Complex.exp (Complex.I * beta)) •
      outerProduct (alignedTarget T s) = 1
    rw [halt, houter, smul_zero, sub_zero]
  have hxs : ∀ x ∈ (((List.range ((L - 1) / 2)).map fun i =>
        -(fullStateReflection s (ylcAlpha L (i + 1) (ylcGamma L delta)) *
          fullTargetReflectionFull (alignedTarget T s)
            (-(ylcAlpha L (L - 1 - i) (ylcGamma L delta)))))).reverse,
      ∃ c : ℂ, x *ᵥ s = c • s := by
    intro x hx
    rw [List.mem_reverse] at hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    rw [htref, mul_one]
    refine ⟨-(Complex.exp (-(Complex.I * ylcAlpha L (i + 1) (ylcGamma L delta)))), ?_⟩
    rw [neg_mulVec, fullStateReflection_mulVec_self hns, neg_smul]
  have hprod : ∃ c : ℂ, fullWordMatrix s (alignedTarget T s) L delta *ᵥ s = c • s := by
    show ∃ c : ℂ, ((List.range ((L - 1) / 2)).map fun i =>
      -(fullStateReflection s (ylcAlpha L (i + 1) (ylcGamma L delta)) *
        fullTargetReflectionFull (alignedTarget T s)
          (-(ylcAlpha L (L - 1 - i) (ylcGamma L delta))))).reverse.prod *ᵥ s = c • s
    exact listProd_smul_self hxs
  obtain ⟨c, hc⟩ := hprod
  show ‖Qatlib.Foundations.PureStateMath.Inner T
      (fullWordMatrix s (alignedTarget T s) L delta *ᵥ s)‖ ^ 2 = 0
  rw [hc, inner_smul_right, hinner, mul_zero]
  simp

/-- Both query and preparation counts are additive in the iterate count. -/
theorem resourceTransport :
    (∀ (l1 l2 : ℕ),
      wordQueryCount (l1 + l2) = wordQueryCount l1 + wordQueryCount l2 ∧
        wordPreparationCount (l1 + l2) = wordPreparationCount l1 +
          wordPreparationCount l2) := by
  intro l1 l2
  simp [wordQueryCount_eq, wordPreparationCount_eq, mul_add]

/-- The inner product with the two-level target basis vector extracts the coordinate at one. -/
private theorem inner_target_two (v : QState (Fin 2)) :
    Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) v = v 1 := by
  rw [inner_apply, Fin.sum_univ_two]
  rw [show (if (0 : Fin 2) = 0 then (0:ℂ) else 1) = 0 from if_pos rfl,
      show (if (1 : Fin 2) = 0 then (0:ℂ) else 1) = 1 from if_neg (by decide)]
  simp

/-- The coordinate at zero of `ampState lam` is the complex coercion of `√(1 - lam)`. -/
private theorem ampState_apply_zero (lam : ℝ) :
    ampState lam 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) := by
  show (if (0 : Fin 2) = 0 then ((Real.sqrt (1 - lam) : ℝ) : ℂ)
    else ((Real.sqrt lam : ℝ) : ℂ)) = _
  exact if_pos rfl

/-- The coordinate at one of `ampState lam` is the complex coercion of `√lam`. -/
private theorem ampState_apply_one (lam : ℝ) :
    ampState lam 1 = ((Real.sqrt lam : ℝ) : ℂ) := by
  show (if (1 : Fin 2) = 0 then ((Real.sqrt (1 - lam) : ℝ) : ℂ)
    else ((Real.sqrt lam : ℝ) : ℂ)) = _
  exact if_neg (by decide)

/-- The inner product with `ampState lam` is the displayed linear combination of the two
coordinates with square-root coefficients. -/
private theorem inner_ampState (lam : ℝ) (u : QState (Fin 2)) :
    Qatlib.Foundations.PureStateMath.Inner (ampState lam) u
      = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * u 0 + ((Real.sqrt lam : ℝ) : ℂ) * u 1 := by
  rw [inner_apply, Fin.sum_univ_two, ampState_apply_zero, ampState_apply_one]
  simp only [Complex.conj_ofReal]

/-- The complex phase `exp(i * π / 3)`. -/
private noncomputable def pi3Phase : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))

/-- The complex exponential at angle `π / 3` is `1 / 2 + i * √3 / 2`. -/
private theorem exp_I_pi_div_three :
    Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))
      = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I
      from mul_comm _ _, Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]

/-- The phase `pi3Phase` has real part `1 / 2` and imaginary part `√3 / 2`. -/
private theorem pi3Phase_val :
    pi3Phase = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I :=
  exp_I_pi_div_three

/-- The exponential of `(-π / 3) * i` is `1 / 2 - i * √3 / 2`. -/
private theorem exp_mul_I_neg_pi_div_three :
    Complex.exp (((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I)
      = ((1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
  push_cast
  ring

/-- The exponential `exp(-(i * (π / 3)))` is `1 / 2 - i * √3 / 2`. -/
private theorem exp_neg_I_pi_div_three :
    Complex.exp (-(Complex.I * ((Real.pi / 3 : ℝ) : ℂ)))
      = ((1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show -(Complex.I * ((Real.pi / 3 : ℝ) : ℂ)) = ((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I
        by push_cast; ring]
  exact exp_mul_I_neg_pi_div_three

/-- The exponential `exp(i * (-π / 3))` is `1 / 2 - i * √3 / 2`. -/
private theorem exp_I_pi_div_three_neg :
    Complex.exp (Complex.I * (((-Real.pi / 3 : ℝ)) : ℂ))
      = ((1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (((-Real.pi / 3 : ℝ)) : ℂ) = ((-(Real.pi / 3) : ℝ) : ℂ) * Complex.I
        by push_cast; ring]
  exact exp_mul_I_neg_pi_div_three

/-- The phase `pi3Phase` satisfies the quadratic relation `z ^ 2 - z + 1 = 0`. -/
private theorem pi3Phase_key : pi3Phase * pi3Phase - pi3Phase + 1 = 0 := by
  rw [pi3Phase_val]
  have h3 : (Real.sqrt 3 / 2 : ℝ) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [h3]
  · norm_num [Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

/-- The negative-angle exponential at `π / 3` equals `1 - pi3Phase`. -/
private theorem pi3Phase_conj :
    Complex.exp (-(Complex.I * ((Real.pi / 3 : ℝ) : ℂ))) = 1 - pi3Phase := by
  rw [exp_neg_I_pi_div_three, pi3Phase_val]
  push_cast
  ring

/-- The exponential `exp(i * (-π / 3))` equals `1 - pi3Phase`. -/
private theorem exp_I_pi_div_three_neg' :
    Complex.exp (Complex.I * (((-Real.pi / 3 : ℝ)) : ℂ)) = 1 - pi3Phase := by
  rw [exp_I_pi_div_three_neg, pi3Phase_val]
  push_cast
  ring

/-- The exponential `exp(-(i * (-π / 3)))` equals `pi3Phase`. -/
private theorem exp_neg_I_pi_div_three_neg :
    Complex.exp (-(Complex.I * (((-Real.pi / 3 : ℝ)) : ℂ))) = pi3Phase := by
  rw [show -(Complex.I * (((-Real.pi / 3 : ℝ)) : ℂ)) = Complex.I * ((Real.pi / 3 : ℝ) : ℂ)
        by push_cast; ring]
  rfl

/-- For real `a` and `b`, the squared modulus of `a + b * pi3Phase` is `a ^ 2 + a * b + b ^ 2`. -/
private theorem normSq_add_mul_pi3Phase (a b : ℝ) :
    Complex.normSq (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * pi3Phase) = a * a + a * b + b * b := by
  rw [pi3Phase_val]
  have hform : (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) *
      (((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      = (((a + b * (1 / 2 : ℝ) : ℝ)) : ℂ) + (((b * (Real.sqrt 3 / 2 : ℝ) : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hform, Complex.normSq_add_mul_I]
  have hsq : (b * (Real.sqrt 3 / 2 : ℝ)) ^ 2 = b * b * (3 / 4) := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hsq]
  ring_nf

/-- If `z - w` is a multiple of the vanishing quadratic expression in `pi3Phase`, then `z = w`. -/
private theorem eq_of_pi3Phase_key {z w : ℂ} (q : ℂ)
    (h : z - w = (pi3Phase * pi3Phase - pi3Phase + 1) * q) : z = w := by
  rw [pi3Phase_key, zero_mul, sub_eq_zero] at h
  exact h

/-- For `lam ∈ [0, 1]` and a vector with the stated square-root-scaled coordinates, the failure
coordinate after a Grover iterate is the displayed phase-dependent expression. -/
private theorem groverIterate_apply_zero {lam : ℝ} (hl : 0 ≤ lam) (hl' : 0 ≤ 1 - lam)
    (alpha beta : ℝ) (v : QState (Fin 2)) (X Y : ℂ)
    (hv0 : v 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * X)
    (hv1 : v 1 = ((Real.sqrt lam : ℝ) : ℂ) * Y) :
    (groverIterate lam alpha beta *ᵥ v) 0
      = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
          (-(1 - (1 - Complex.exp (-(Complex.I * alpha))) * ((1 - lam : ℝ) : ℂ)) * X
            + (1 - Complex.exp (-(Complex.I * alpha))) * ((lam : ℝ) : ℂ)
                * Complex.exp (Complex.I * beta) * Y) := by
  have hsq1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ)
      = ((1 - lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl']
  have hsq2 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = ((lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  have hD : ∀ (w : QState (Fin 2)) (x : Fin 2),
      (targetReflection beta *ᵥ w) x
        = (if x = 0 then (1:ℂ) else Complex.exp (Complex.I * beta)) * w x := by
    intro w x
    show (Matrix.diagonal (fun i => if i = 0 then (1:ℂ) else Complex.exp (Complex.I * beta))
      *ᵥ w) x = _
    rw [Matrix.mulVec_diagonal]
  have hS : ∀ (w : QState (Fin 2)) (x : Fin 2),
      (stateReflection lam alpha *ᵥ w) x
        = w x - (1 - Complex.exp (-(Complex.I * alpha))) * Qatlib.Foundations.PureStateMath.Inner (ampState lam) w
            * (ampState lam) x := by
    intro w x
    show ((1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct (ampState lam))
      *ᵥ w) x = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outerProduct_mulVec,
      smul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hu0 : (targetReflection beta *ᵥ v) 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * X := by
    rw [hD, show (if (0 : Fin 2) = 0 then (1:ℂ) else Complex.exp (Complex.I * beta)) = 1
        from if_pos rfl, one_mul, hv0]
  have hin : Qatlib.Foundations.PureStateMath.Inner (ampState lam) (targetReflection beta *ᵥ v)
      = ((1 - lam : ℝ) : ℂ) * X + ((lam : ℝ) : ℂ) * Complex.exp (Complex.I * beta) * Y := by
    rw [inner_ampState, hu0, hD,
      show (if (1 : Fin 2) = 0 then (1:ℂ) else Complex.exp (Complex.I * beta))
        = Complex.exp (Complex.I * beta) from if_neg (by decide), hv1]
    have e1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * (((Real.sqrt (1 - lam) : ℝ) : ℂ) * X)
        = ((1 - lam : ℝ) : ℂ) * X := by
      rw [← mul_assoc, hsq1]
    have e2 : ((Real.sqrt lam : ℝ) : ℂ) *
        (Complex.exp (Complex.I * beta) * (((Real.sqrt lam : ℝ) : ℂ) * Y))
        = ((lam : ℝ) : ℂ) * Complex.exp (Complex.I * beta) * Y := by
      rw [show ((Real.sqrt lam : ℝ) : ℂ) *
          (Complex.exp (Complex.I * beta) * (((Real.sqrt lam : ℝ) : ℂ) * Y))
          = (((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ))
              * Complex.exp (Complex.I * beta) * Y by ring, hsq2]
    rw [e1, e2]
  have hG : groverIterate lam alpha beta = -(stateReflection lam alpha * targetReflection beta) :=
    rfl
  rw [hG, Matrix.neg_mulVec, Pi.neg_apply, ← Matrix.mulVec_mulVec, hS, hu0, hin,
    ampState_apply_zero]
  ring

/-- For `lam ∈ [0, 1]` and a vector with the stated square-root-scaled coordinates, the success
coordinate after a Grover iterate is the displayed phase-dependent expression. -/
private theorem groverIterate_apply_one {lam : ℝ} (hl : 0 ≤ lam) (hl' : 0 ≤ 1 - lam)
    (alpha beta : ℝ) (v : QState (Fin 2)) (X Y : ℂ)
    (hv0 : v 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * X)
    (hv1 : v 1 = ((Real.sqrt lam : ℝ) : ℂ) * Y) :
    (groverIterate lam alpha beta *ᵥ v) 1
      = ((Real.sqrt lam : ℝ) : ℂ) *
          ((1 - Complex.exp (-(Complex.I * alpha))) * ((1 - lam : ℝ) : ℂ) * X
            - (1 - (1 - Complex.exp (-(Complex.I * alpha))) * ((lam : ℝ) : ℂ))
                * Complex.exp (Complex.I * beta) * Y) := by
  have hsq1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ)
      = ((1 - lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl']
  have hsq2 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = ((lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  have hD : ∀ (w : QState (Fin 2)) (x : Fin 2),
      (targetReflection beta *ᵥ w) x
        = (if x = 0 then (1:ℂ) else Complex.exp (Complex.I * beta)) * w x := by
    intro w x
    show (Matrix.diagonal (fun i => if i = 0 then (1:ℂ) else Complex.exp (Complex.I * beta))
      *ᵥ w) x = _
    rw [Matrix.mulVec_diagonal]
  have hS : ∀ (w : QState (Fin 2)) (x : Fin 2),
      (stateReflection lam alpha *ᵥ w) x
        = w x - (1 - Complex.exp (-(Complex.I * alpha))) * Qatlib.Foundations.PureStateMath.Inner (ampState lam) w
            * (ampState lam) x := by
    intro w x
    show ((1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct (ampState lam))
      *ᵥ w) x = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outerProduct_mulVec,
      smul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hu0 : (targetReflection beta *ᵥ v) 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * X := by
    rw [hD, show (if (0 : Fin 2) = 0 then (1:ℂ) else Complex.exp (Complex.I * beta)) = 1
        from if_pos rfl, one_mul, hv0]
  have hin : Qatlib.Foundations.PureStateMath.Inner (ampState lam) (targetReflection beta *ᵥ v)
      = ((1 - lam : ℝ) : ℂ) * X + ((lam : ℝ) : ℂ) * Complex.exp (Complex.I * beta) * Y := by
    rw [inner_ampState, hu0, hD,
      show (if (1 : Fin 2) = 0 then (1:ℂ) else Complex.exp (Complex.I * beta))
        = Complex.exp (Complex.I * beta) from if_neg (by decide), hv1]
    have e1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * (((Real.sqrt (1 - lam) : ℝ) : ℂ) * X)
        = ((1 - lam : ℝ) : ℂ) * X := by
      rw [← mul_assoc, hsq1]
    have e2 : ((Real.sqrt lam : ℝ) : ℂ) *
        (Complex.exp (Complex.I * beta) * (((Real.sqrt lam : ℝ) : ℂ) * Y))
        = ((lam : ℝ) : ℂ) * Complex.exp (Complex.I * beta) * Y := by
      rw [show ((Real.sqrt lam : ℝ) : ℂ) *
          (Complex.exp (Complex.I * beta) * (((Real.sqrt lam : ℝ) : ℂ) * Y))
          = (((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ))
              * Complex.exp (Complex.I * beta) * Y by ring, hsq2]
    rw [e1, e2]
  have hG : groverIterate lam alpha beta = -(stateReflection lam alpha * targetReflection beta) :=
    rfl
  rw [hG, Matrix.neg_mulVec, Pi.neg_apply, ← Matrix.mulVec_mulVec, hS,
    hD, show (if (1 : Fin 2) = 0 then (1:ℂ) else Complex.exp (Complex.I * beta))
      = Complex.exp (Complex.I * beta) from if_neg (by decide), hv1, hin,
    ampState_apply_one]
  ring

/-- The positive-angle exponential at `π / 3` equals the defined phase `pi3Phase`. -/
private theorem exp_I_pi_div_three_eq :
    Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ)) = pi3Phase := rfl

/-- For `lam ∈ [0, 1]`, one Grover iterate with phases `-π / 3` and `π / 3` has target
probability `1 - (1 - lam) ^ 3`. -/
theorem pi3_step_response (lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1)
      (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam)‖ ^ 2 =
    1 - (1 - lam) ^ 3 := by
  have hsub : 0 ≤ 1 - lam := by linarith
  have a0 : ampState lam 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * 1 := by
    rw [ampState_apply_zero, mul_one]
  have a1 : ampState lam 1 = ((Real.sqrt lam : ℝ) : ℂ) * 1 := by
    rw [ampState_apply_one, mul_one]
  have hstep : (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam) 1
      = ((Real.sqrt lam : ℝ) : ℂ) * (((1 : ℝ) : ℂ) + (((lam - 2 : ℝ) : ℂ) * pi3Phase)) := by
    rw [groverIterate_apply_one hlam hsub (-Real.pi / 3) (Real.pi / 3) _ _ _ a0 a1,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt lam : ℝ) : ℂ)) * (-(lam : ℂ))) ?_
    push_cast
    ring
  rw [← Complex.normSq_eq_norm_sq, inner_target_two, hstep, Complex.normSq_mul,
    Complex.normSq_ofReal, Real.mul_self_sqrt hlam, normSq_add_mul_pi3Phase]
  ring

/-- For `lam ∈ [0, 1]`, the displayed nesting of the constant `-π / 3` phase schedules has
target probability `1 - (1 - lam) ^ 9`. -/
theorem pi3_nested_response (lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1)
      (nestedWordMatrix (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 lam
        *ᵥ ampState lam)‖ ^ 2 =
    1 - (1 - lam) ^ 9 := by
  have hsub : 0 ≤ 1 - lam := by linarith
  have np1 : nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 1
      = -Real.pi / 3 := rfl
  have np2 : nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 2
      = Real.pi / 3 := by
    have h : nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 2
        = -(-Real.pi / 3) := rfl
    rw [h]
    ring
  have np3 : nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 3
      = -Real.pi / 3 := rfl
  have np4 : nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 4
      = -Real.pi / 3 := rfl
  have hword : nestedWordMatrix (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 lam
      = groverIterate lam (-Real.pi / 3) (Real.pi / 3) *
          (groverIterate lam (-Real.pi / 3) (-Real.pi / 3) *
            (groverIterate lam (Real.pi / 3) (Real.pi / 3) *
              groverIterate lam (-Real.pi / 3) (Real.pi / 3))) := by
    show ((List.range 4).map fun i =>
        groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 (i + 1))
          (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 (4 - i)))).reverse.prod = _
    have hlist : ((List.range 4).map fun i =>
        groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 (i + 1))
          (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 (4 - i)))).reverse
        = [groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 4)
              (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 1)),
           groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 3)
              (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 2)),
           groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 2)
              (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 3)),
           groverIterate lam (nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 1)
              (-(nestedPhase (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 4))] := rfl
    rw [hlist, np1, np2, np3, np4, show -(-Real.pi / 3) = Real.pi / 3 by ring,
      show -(Real.pi / 3) = -Real.pi / 3 by ring]
    rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
  have a0 : ampState lam 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * 1 := by
    rw [ampState_apply_zero, mul_one]
  have a1 : ampState lam 1 = ((Real.sqrt lam : ℝ) : ℂ) * 1 := by
    rw [ampState_apply_one, mul_one]
  rw [← Complex.normSq_eq_norm_sq, inner_target_two]

  have h10 : (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam) 0
      = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * (pi3Phase * (((lam : ℝ) : ℂ) - 1)) := by
    rw [groverIterate_apply_zero hlam hsub (-Real.pi / 3) (Real.pi / 3) _ _ _ a0 a1,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt (1 - lam) : ℝ) : ℂ)) * (-(lam : ℂ))) ?_
    push_cast
    ring
  have h11 : (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam) 1
      = ((Real.sqrt lam : ℝ) : ℂ) * (((1 : ℝ) : ℂ) + (((lam - 2 : ℝ) : ℂ) * pi3Phase)) := by
    rw [groverIterate_apply_one hlam hsub (-Real.pi / 3) (Real.pi / 3) _ _ _ a0 a1,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt lam : ℝ) : ℂ)) * (-(lam : ℂ))) ?_
    push_cast
    ring

  have h20 : (groverIterate lam (Real.pi / 3) (Real.pi / 3) *ᵥ
        (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam)) 0
      = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
          ((1 - (lam : ℂ)) + pi3Phase * (2 * (lam : ℂ) - (lam : ℂ) ^ 2)) := by
    rw [groverIterate_apply_zero hlam hsub (Real.pi / 3) (Real.pi / 3) _ _ _ h10 h11,
      pi3Phase_conj, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt (1 - lam) : ℝ) : ℂ)) *
      (pi3Phase * (lam : ℂ) ^ 2 - 2 * pi3Phase * (lam : ℂ) + (lam : ℂ) - 1)) ?_
    push_cast
    ring
  have h21 : (groverIterate lam (Real.pi / 3) (Real.pi / 3) *ᵥ
        (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam)) 1
      = ((Real.sqrt lam : ℝ) : ℂ) *
          (-1 + pi3Phase * (2 * (lam : ℂ) - (lam : ℂ) ^ 2)) := by
    rw [groverIterate_apply_one hlam hsub (Real.pi / 3) (Real.pi / 3) _ _ _ h10 h11,
      pi3Phase_conj, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt lam : ℝ) : ℂ)) *
      (pi3Phase * (lam : ℂ) ^ 2 - 2 * pi3Phase * (lam : ℂ) + 1)) ?_
    push_cast
    ring

  have h30 : (groverIterate lam (-Real.pi / 3) (-Real.pi / 3) *ᵥ
        (groverIterate lam (Real.pi / 3) (Real.pi / 3) *ᵥ
          (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam))) 0
      = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
          ((lam : ℂ) + pi3Phase * ((lam : ℂ) ^ 3 - 2 * (lam : ℂ) ^ 2 + (lam : ℂ) - 1)) := by
    rw [groverIterate_apply_zero hlam hsub (-Real.pi / 3) (-Real.pi / 3) _ _ _ h20 h21,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_neg']
    refine eq_of_pi3Phase_key ((((Real.sqrt (1 - lam) : ℝ) : ℂ)) *
      (-pi3Phase * (lam : ℂ) ^ 3 + 2 * pi3Phase * (lam : ℂ) ^ 2 + (lam : ℂ) ^ 2 - 3 * (lam : ℂ))) ?_
    push_cast
    ring
  have h31 : (groverIterate lam (-Real.pi / 3) (-Real.pi / 3) *ᵥ
        (groverIterate lam (Real.pi / 3) (Real.pi / 3) *ᵥ
          (groverIterate lam (-Real.pi / 3) (Real.pi / 3) *ᵥ ampState lam))) 1
      = ((Real.sqrt lam : ℝ) : ℂ) *
          (((lam : ℂ) ^ 2 - 2 * (lam : ℂ) + 2)
            + pi3Phase * ((lam : ℂ) ^ 3 - 3 * (lam : ℂ) ^ 2 + 3 * (lam : ℂ) - 2)) := by
    rw [groverIterate_apply_one hlam hsub (-Real.pi / 3) (-Real.pi / 3) _ _ _ h20 h21,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_neg']
    refine eq_of_pi3Phase_key ((((Real.sqrt lam : ℝ) : ℂ)) *
      (-pi3Phase * (lam : ℂ) ^ 3 + 2 * pi3Phase * (lam : ℂ) ^ 2 - (lam : ℂ))) ?_
    push_cast
    ring

  have hfin : (nestedWordMatrix (fun _ => -Real.pi / 3) (fun _ => -Real.pi / 3) 1 1 lam
        *ᵥ ampState lam) 1
      = ((Real.sqrt lam : ℝ) : ℂ) *
          ((((-lam ^ 4 + 5 * lam ^ 3 - 9 * lam ^ 2 + 8 * lam - 3 : ℝ)) : ℂ)
            + (((lam ^ 4 - 4 * lam ^ 3 + 6 * lam ^ 2 - 4 * lam : ℝ)) : ℂ) * pi3Phase) := by
    rw [hword, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [groverIterate_apply_one hlam hsub (-Real.pi / 3) (Real.pi / 3) _ _ _ h30 h31,
      exp_neg_I_pi_div_three_neg, exp_I_pi_div_three_eq]
    refine eq_of_pi3Phase_key ((((Real.sqrt lam : ℝ) : ℂ)) *
      (-pi3Phase * (lam : ℂ) ^ 4 + 3 * pi3Phase * (lam : ℂ) ^ 3 - 3 * pi3Phase * (lam : ℂ) ^ 2
        + 2 * pi3Phase * (lam : ℂ) + (lam : ℂ) ^ 4 - 5 * (lam : ℂ) ^ 3 + 8 * (lam : ℂ) ^ 2
        - 7 * (lam : ℂ) + 3)) ?_
    push_cast
    ring
  rw [hfin, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hlam,
    normSq_add_mul_pi3Phase]
  ring

/-- The two-level target basis vector with coordinates zero and one. -/
def ylcTargetVec : QState (Fin 2) := fun i => if i = 0 then (0:ℂ) else 1

/-- The two-level failure basis vector with coordinates one and zero. -/
def ylcFailVec : QState (Fin 2) := fun i => if i = 0 then (1:ℂ) else 0

/-- The target basis vector has coordinate zero at index zero. -/
@[simp] theorem ylcTargetVec_zero : ylcTargetVec 0 = 0 := by
  show (if (0 : Fin 2) = 0 then (0:ℂ) else 1) = 0
  simp

/-- The target basis vector has coordinate one at index one. -/
@[simp] theorem ylcTargetVec_one : ylcTargetVec 1 = 1 := by
  show (if (1 : Fin 2) = 0 then (0:ℂ) else 1) = 1
  simp

/-- The failure basis vector has coordinate one at index zero. -/
@[simp] theorem ylcFailVec_zero : ylcFailVec 0 = 1 := by
  show (if (0 : Fin 2) = 0 then (1:ℂ) else 0) = 1
  simp

/-- The failure basis vector has coordinate zero at index one. -/
@[simp] theorem ylcFailVec_one : ylcFailVec 1 = 0 := by
  show (if (1 : Fin 2) = 0 then (1:ℂ) else 0) = 0
  simp

/-- The inner product with `ylcTargetVec` extracts the coordinate at one. -/
theorem inner_ylcTargetVec (ψ : QState (Fin 2)) : Qatlib.Foundations.PureStateMath.Inner ylcTargetVec ψ = ψ 1 := by
  rw [inner_apply, Fin.sum_univ_two, ylcTargetVec_zero, ylcTargetVec_one]
  simp

/-- The inner product with `ylcFailVec` extracts the coordinate at zero. -/
theorem inner_ylcFailVec (ψ : QState (Fin 2)) : Qatlib.Foundations.PureStateMath.Inner ylcFailVec ψ = ψ 0 := by
  rw [inner_apply, Fin.sum_univ_two, ylcFailVec_zero, ylcFailVec_one]
  simp

/-- The squared target and failure overlaps sum to the sum of squared coordinate norms of a
two-component state. -/
theorem two_component_normSq (ψ : QState (Fin 2)) :
    ‖Qatlib.Foundations.PureStateMath.Inner ylcTargetVec ψ‖ ^ 2 + ‖Qatlib.Foundations.PureStateMath.Inner ylcFailVec ψ‖ ^ 2 = ∑ i, ‖ψ i‖ ^ 2 := by
  rw [inner_ylcTargetVec, inner_ylcFailVec, Fin.sum_univ_two]
  exact add_comm _ _

/-- For `lam ∈ [0, 1]`, the amplitude state is normalized. -/
theorem ampState_normalized {lam : ℝ} (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    Normalized (ampState lam) := by
  have h0 : ampState lam 0 = (Real.sqrt (1 - lam) : ℂ) := by
    show ((if (0 : Fin 2) = 0 then Real.sqrt (1 - lam) else Real.sqrt lam : ℝ) : ℂ) = _
    simp
  have h1 : ampState lam 1 = (Real.sqrt lam : ℂ) := by
    show ((if (1 : Fin 2) = 0 then Real.sqrt (1 - lam) else Real.sqrt lam : ℝ) : ℂ) = _
    simp
  have h0n : ‖ampState lam 0‖ ^ 2 = 1 - lam := by
    rw [h0, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (by linarith)
  have h1n : ‖ampState lam 1‖ ^ 2 = lam := by
    rw [h1, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt hl
  unfold Normalized
  rw [Fin.sum_univ_two, h0n, h1n]
  linarith

/-- A complex number of norm one multiplied by its complex conjugate is one. -/
theorem star_mul_self_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
  simp

/-- For a real phase `alpha`, the exponential `exp(-i * alpha)` has norm one. -/
theorem norm_exp_neg_I_mul (alpha : ℝ) :
    ‖Complex.exp (-(Complex.I * (alpha : ℂ)))‖ = 1 := by
  have h : -(Complex.I * (alpha : ℂ)) = (((-alpha : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The phase difference `1 - exp(-i * alpha)` plus its conjugate equals its squared modulus
expressed as a conjugate product. -/
theorem ylcPhase_key (alpha : ℝ) :
    (1 - Complex.exp (-(Complex.I * (alpha : ℂ)))) +
      (starRingEnd ℂ) (1 - Complex.exp (-(Complex.I * (alpha : ℂ)))) =
    (starRingEnd ℂ) (1 - Complex.exp (-(Complex.I * (alpha : ℂ)))) *
      (1 - Complex.exp (-(Complex.I * (alpha : ℂ)))) := by
  set e : ℂ := Complex.exp (-(Complex.I * (alpha : ℂ))) with he
  have hconjE : (starRingEnd ℂ) e = Complex.exp (Complex.I * (alpha : ℂ)) := by
    rw [he, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hnorm : ‖e‖ = 1 := by rw [he, norm_exp_neg_I_mul]
  rw [map_sub, map_one]
  have hme : (starRingEnd ℂ) e * e = 1 := star_mul_self_eq_one hnorm
  rw [mul_sub, mul_one, sub_mul, one_mul, hme]
  ring

/-- Every real target phase defines a unitary target reflection. -/
theorem targetReflection_unitary (beta : ℝ) :
    targetReflection beta ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  set d : Fin 2 → ℂ := fun k => if k = 0 then (1:ℂ) else Complex.exp (Complex.I * (beta:ℂ))
    with hd0
  have hdef : targetReflection beta = Matrix.diagonal d := by
    rw [hd0]
    rfl
  rw [hdef]
  have hd : ∀ i : Fin 2, (star d) i * d i = 1 := by
    intro i
    rcases (show i = 0 ∨ i = 1 by revert i; decide) with h | h
    · subst h
      show (star d) 0 * d 0 = 1
      rw [hd0]
      simp
    · subst h
      show (star d) 1 * d 1 = 1
      rw [hd0]
      simp
      exact star_mul_self_eq_one (by
        rw [show Complex.I * (beta : ℂ) = (beta : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I])
  have hdiag : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have h : (fun i : Fin 2 => (star d) i * d i) = fun _ => (1:ℂ) := funext hd
    rw [h]
    exact Matrix.diagonal_one
  exact hdiag

/-- For `lam ∈ [0, 1]`, the source reflection is unitary for every real phase. -/
theorem stateReflection_unitary {lam alpha : ℝ} (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    stateReflection lam alpha ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hnorm : Normalized (ampState lam) := ampState_normalized hl hl'
  have hP := isOrthogonalProjector_outerProduct hnorm
  have hPP : outerProduct (ampState lam) * outerProduct (ampState lam)
      = outerProduct (ampState lam) := hP.1
  have hPst : (outerProduct (ampState lam))ᴴ = outerProduct (ampState lam) := hP.2
  set P : Matrix (Fin 2) (Fin 2) ℂ := outerProduct (ampState lam)
  set c : ℂ := 1 - Complex.exp (-(Complex.I * (alpha : ℂ))) with hc
  have hS : stateReflection lam alpha = 1 - c • P := by
    show (1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct (ampState lam))
        = 1 - c • P
    rw [hc]
  rw [hS]
  have hkey : ((1 - c • P)ᴴ : Matrix (Fin 2) (Fin 2) ℂ) * (1 - c • P)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) - (c + (starRingEnd ℂ) c - (starRingEnd ℂ) c * c) • P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hPst]
    have hss : (star c : ℂ) = (starRingEnd ℂ) c := rfl
    rw [hss]
    have hm : ((starRingEnd ℂ) c • P) * (c • P) = ((starRingEnd ℂ) c * c) • P := by
      rw [smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
    have hexp : (1 - (starRingEnd ℂ) c • P) * (1 - c • P)
        = 1 - c • P - ((starRingEnd ℂ) c • P) + ((starRingEnd ℂ) c • P) * (c • P) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [hexp, hm]
    have hdist : (c + (starRingEnd ℂ) c - (starRingEnd ℂ) c * c) • P
        = c • P + (starRingEnd ℂ) c • P - ((starRingEnd ℂ) c * c) • P := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hdist]
    abel
  rw [hkey]
  have hscal : c + (starRingEnd ℂ) c - (starRingEnd ℂ) c * c = 0 := by
    have h := ylcPhase_key alpha
    have hc0 : c = 1 - Complex.exp (-(Complex.I * (alpha : ℂ))) := hc
    rw [hc0]
    have h3 : ((1 - Complex.exp (-(Complex.I * (alpha : ℂ))))
        + (starRingEnd ℂ) (1 - Complex.exp (-(Complex.I * (alpha : ℂ))))
        - (starRingEnd ℂ) (1 - Complex.exp (-(Complex.I * (alpha : ℂ)))) *
          (1 - Complex.exp (-(Complex.I * (alpha : ℂ))))) = 0 := by
      rw [h, sub_self]
    exact h3
  rw [hscal, zero_smul, sub_zero]

/-- The negative of a unitary two-by-two matrix is unitary. -/
theorem neg_mem_unitary {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) : -M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.conjTranspose_neg, neg_mul_neg]
  exact hM

/-- The product of two unitary two-by-two matrices is unitary. -/
theorem mul_mem_unitary {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    A * B ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA hB ⊢
  rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc Aᴴ, hA, one_mul, hB]

/-- For `lam ∈ [0, 1]`, every generalized Grover iterate with real phases is unitary. -/
theorem groverIterate_unitary {lam alpha beta : ℝ} (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    groverIterate lam alpha beta ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  show -(stateReflection lam alpha * targetReflection beta) ∈ Matrix.unitaryGroup (Fin 2) ℂ
  exact neg_mem_unitary (mul_mem_unitary (stateReflection_unitary hl hl')
    (targetReflection_unitary beta))

/-- The product of a list of unitary two-by-two matrices is unitary. -/
private theorem list_prod_unitary {xs : List (Matrix (Fin 2) (Fin 2) ℂ)}
    (h : ∀ x ∈ xs, x ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    xs.prod ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction xs with
  | nil =>
    rw [List.prod_nil]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    simp
  | cons x xs ih =>
    rw [List.prod_cons]
    exact mul_mem_unitary (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- For `lam ∈ [0, 1]`, the analytic fixed-point word matrix is unitary. -/
theorem ylcWordMatrix_unitary (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    ylcWordMatrix l delta lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  show (((List.range l).map fun i =>
      groverIterate lam (ylcAlpha (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta))
        (-(ylcAlpha (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)))).reverse.prod) ∈ _
  apply list_prod_unitary
  intro x hx
  rw [List.mem_reverse] at hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact groverIterate_unitary hl hl'

/-- The complex recurrence coefficient given by the ratio of conjugate cosine-sine expressions
at angle `(h - 1) * π / L`. -/
noncomputable def ylcRecW (L : ℕ) (mu : ℝ) (h : ℕ) : ℂ :=
  let phi : ℝ := ((h - 1 : ℕ) : ℝ) * Real.pi / (L : ℝ)
  (((Real.cos phi : ℝ) : ℂ) - Complex.I * (mu : ℂ) * ((Real.sin phi : ℝ) : ℂ)) /
    (((Real.cos phi : ℝ) : ℂ) + Complex.I * (mu : ℂ) * ((Real.sin phi : ℝ) : ℂ))

/-- The second-order amplitude recurrence with initial values one and `x`, weighted by
`ylcRecW`, corresponding to the recurrence in [YoderLowChuang2014]. -/
noncomputable def ylcRecA (L : ℕ) (mu x : ℝ) : ℕ → ℂ
  | 0 => 1
  | 1 => (x : ℂ)
  | h + 2 => (x : ℂ) * (1 + ylcRecW L mu (h + 2)) * ylcRecA L mu x (h + 1)
      - ylcRecW L mu (h + 2) * ylcRecA L mu x h

/-- The proposition that, for positive odd length and valid probability parameters, the word's
failure amplitude is a unit-modulus scalar times the final recurrence value. -/
def ylcBridgeRec_rearrangement : Prop :=
  ∀ (L : ℕ) (delta lam : ℝ), Odd L → 1 ≤ L → 0 < delta → delta < 1 →
    0 ≤ lam → lam ≤ 1 →
    ∃ c : ℂ, ‖c‖ = 1 ∧
      Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (1:ℂ) else 0)
          (ylcWordMatrix ((L - 1) / 2) delta lam *ᵥ ampState lam) =
        c * ylcRecA L (Real.sqrt (1 - ylcGamma L delta ^ 2)) (Real.sqrt (1 - lam)) L

/-- The proposition that, for positive odd length and valid probability parameters, the final
recurrence value equals the scaled Chebyshev evaluation of [YoderLowChuang2014]. -/
def ylcBridgeRec_miracle : Prop :=
  ∀ (L : ℕ) (delta lam : ℝ), Odd L → 1 ≤ L → 0 < delta → delta < 1 →
    0 ≤ lam → lam ≤ 1 →
    ylcRecA L (Real.sqrt (1 - ylcGamma L delta ^ 2)) (Real.sqrt (1 - lam)) L =
      (delta * cheb L (Real.sqrt (1 - lam) / ylcGamma L delta) : ℂ)

/-- Assuming the rearrangement and Chebyshev recurrence bridges, the word's target probability
equals `responseProb (2 * l + 1) delta lam` for `0 < delta < 1` and `lam ∈ [0, 1]`
[YoderLowChuang2014]. -/
theorem ylc_master_response_of_bridges
    (hre : ylcBridgeRec_rearrangement) (hmi : ylcBridgeRec_miracle) :
    ∀ (l : ℕ) (delta lam : ℝ), 0 < delta → delta < 1 → 0 ≤ lam → lam ≤ 1 →
      ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1)
        (ylcWordMatrix l delta lam *ᵥ ampState lam)‖ ^ 2 =
      responseProb (2 * l + 1) delta lam := by
  intro l delta lam hd hd' hlam hlam'
  have hLodd : Odd (2 * l + 1) := ⟨l, by ring⟩
  have hL1 : 1 ≤ (2 * l + 1 : ℕ) := by omega
  have hhalf : ((2 * l + 1 : ℕ) - 1) / 2 = l := by omega
  obtain ⟨c, hc, hamp⟩ := hre (2 * l + 1) delta lam hLodd hL1 hd hd' hlam hlam'
  have hmi' := hmi (2 * l + 1) delta lam hLodd hL1 hd hd' hlam hlam'
  have hfail : ‖Qatlib.Foundations.PureStateMath.Inner ylcFailVec (ylcWordMatrix l delta lam *ᵥ ampState lam)‖ ^ 2
      = (delta * cheb (2 * l + 1) (Real.sqrt (1 - lam) / ylcGamma (2 * l + 1) delta)) ^ 2 := by
    have h0 : ylcWordMatrix l delta lam
        = ylcWordMatrix (((2 * l + 1 : ℕ) - 1) / 2) delta lam := by
      rw [hhalf]
    show ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (1:ℂ) else 0)
        (ylcWordMatrix l delta lam *ᵥ ampState lam)‖ ^ 2 = _
    rw [h0, hamp, hmi', norm_mul, hc, one_mul]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofReal]
    ring
  have hψ : Normalized (ylcWordMatrix l delta lam *ᵥ ampState lam) := by
    have hU := ylcWordMatrix_unitary l delta lam hlam hlam'
    have hs := ampState_normalized hlam hlam'
    simpa [ApplyGate] using normalized_applyGate hU hs
  have htwo := two_component_normSq (ylcWordMatrix l delta lam *ᵥ ampState lam)
  have hfin : ‖Qatlib.Foundations.PureStateMath.Inner ylcTargetVec (ylcWordMatrix l delta lam *ᵥ ampState lam)‖ ^ 2
      = 1 - (delta * cheb (2 * l + 1) (Real.sqrt (1 - lam) / ylcGamma (2 * l + 1) delta)) ^ 2 := by
    have hsum : (∑ i, ‖(ylcWordMatrix l delta lam *ᵥ ampState lam) i‖ ^ 2) = 1 := hψ
    linarith [htwo, hfail]
  show ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1)
      (ylcWordMatrix l delta lam *ᵥ ampState lam)‖ ^ 2 =
    responseProb (2 * l + 1) delta lam
  rw [responseProb_eq]
  exact hfin

/-- For `0 < delta < 1` and `lam ∈ [0, 1]`, the zero-iterate word's target probability equals
the length-one Chebyshev response. -/
theorem ylc_master_response_zero (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1)
      (ylcWordMatrix 0 delta lam *ᵥ ampState lam)‖ ^ 2 =
    responseProb 1 delta lam := by
  have hW : ylcWordMatrix 0 delta lam = 1 := by
    show ((List.range 0).map fun i =>
      groverIterate lam (ylcAlpha 1 (i + 1) (ylcGamma 1 delta))
        (-(ylcAlpha 1 (0 - i) (ylcGamma 1 delta)))).reverse.prod = 1
    simp
  have hamp : Qatlib.Foundations.PureStateMath.Inner (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) (ampState lam)
      = (Real.sqrt lam : ℂ) := by
    have h0 : ampState lam 0 = (Real.sqrt (1 - lam) : ℂ) := by
      show ((if (0 : Fin 2) = 0 then Real.sqrt (1 - lam) else Real.sqrt lam : ℝ) : ℂ) = _
      simp
    have h1 : ampState lam 1 = (Real.sqrt lam : ℂ) := by
      show ((if (1 : Fin 2) = 0 then Real.sqrt (1 - lam) else Real.sqrt lam : ℝ) : ℂ) = _
      simp
    rw [inner_apply, Fin.sum_univ_two, h0, h1]
    simp
  have hγ : ylcGamma 1 delta = delta := by
    have h1 : 1 ≤ 1 / delta := one_le_one_div_of_le hd (le_of_lt hd')
    rw [ylcGamma, show ((1 : ℕ) : ℝ) = 1 by norm_num, div_one, Real.cosh_arcosh h1,
      one_div_one_div]
  have hresp : responseProb 1 delta lam = lam := by
    rw [responseProb_eq, hγ, cheb_one]
    have h : delta * (Real.sqrt (1 - lam) / delta) = Real.sqrt (1 - lam) := by
      field_simp
    rw [h]
    nlinarith [Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ 1 - lam)]
  rw [hW, Matrix.one_mulVec, hamp, hresp]
  have hnorm : ‖(Real.sqrt lam : ℂ)‖ ^ 2 = lam := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt hlam
  exact hnorm

end Qatlib.Papers.FixedPtSearch14.FixedPoint
