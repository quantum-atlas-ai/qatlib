/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Finite-dimensional estimates for an adiabatic lower bound

This module proves overlap and squared-distance inequalities used in the finite-dimensional
adiabatic runtime argument. The theorem `overlap_sum_le_sqrt_mul` controls normalized vectors in
a common finite orthonormal span, `eq10_lower_bound_with_sqrt` inserts this overlap bound into
the distance estimate, and `deriv_abs_integral_bound` integrates the specified derivative bound.
The mathematical context is [FarhiGoldstoneGutmannNagaj2008].

## Main statements

* `overlap_sum_le_sqrt_mul`: For an orthonormal family of size `N` and unit vectors lying in the
  span of an orthonormal family of size `k`, the sum of the corresponding absolute overlaps is
  at most `Real.sqrt (N * k)`.
* `eq10_lower_bound_with_sqrt`: Under the unit-vector and orthogonality hypotheses, an
  overlap-sum bound `Real.sqrt (N * k)` gives the squared-distance lower bound `2 * N * (1 -
  Real.sqrt (1 - b)) - 2 * Real.sqrt b * Real.sqrt (N * k)` for `b ∈ [0, 1]`.
* `deriv_abs_integral_bound`: For nonnegative `T`, if `S T = 0`, the derivative exists and is
  interval integrable, and `|deriv S t| ≤ 2 * E * (1 - t / T) * K` on the interval, then `S 0 ≤
  E * T * K`.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmannNagaj2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.MainResults

open scoped BigOperators ComplexInnerProductSpace
open Finset intervalIntegral MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- For an orthonormal family of size `N` and unit vectors lying in the span of an orthonormal
family of size `k`, the sum of the corresponding absolute overlaps is at most `Real.sqrt (N
* k)` [FarhiGoldstoneGutmannNagaj2008]. -/
theorem overlap_sum_le_sqrt_mul
    (N k : ℕ) (e : Fin N → V) (he : Orthonormal ℂ e)
    (v : Fin k → V) (hv : Orthonormal ℂ v)
    (a : Fin N → Fin k → ℂ)
    (i : Fin N → V) (hi : ∀ x, i x = ∑ j, a x j • v j)
    (hni : ∀ x, ‖i x‖ = 1) :
    ∑ x : Fin N, ‖⟪e x, i x⟫‖ ≤ Real.sqrt ((N : ℝ) * (k : ℝ)) := by

  have hxi : ∀ x : Fin N, ‖⟪e x, i x⟫‖ ≤ ∑ j : Fin k, ‖a x j‖ * ‖⟪e x, v j⟫‖ := by
    intro x
    rw [hi x, inner_sum]
    calc ‖∑ j : Fin k, ⟪e x, a x j • v j⟫‖
        ≤ ∑ j : Fin k, ‖⟪e x, a x j • v j⟫‖ := norm_sum_le _ _
      _ = ∑ j : Fin k, ‖a x j‖ * ‖⟪e x, v j⟫‖ := by
          refine sum_congr rfl fun j _ => ?_
          rw [inner_smul_right, norm_mul]
  have hsum_le :
      ∑ x : Fin N, ‖⟪e x, i x⟫‖
        ≤ ∑ x : Fin N, ∑ j : Fin k, ‖a x j‖ * ‖⟪e x, v j⟫‖ :=
    sum_le_sum fun x _ => hxi x

  have ha_norm : ∀ x : Fin N, ∑ j : Fin k, ‖a x j‖ ^ 2 = 1 := by
    intro x
    have hinner := hv.inner_sum (a x) (a x) (Finset.univ : Finset (Fin k))
    have h1 : ((‖i x‖ ^ 2 : ℝ) : ℂ) = ∑ j : Fin k, ((‖a x j‖ ^ 2 : ℝ) : ℂ) := by
      have hii : ((‖i x‖ ^ 2 : ℝ) : ℂ) = ⟪i x, i x⟫ := by
        rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
        rfl
      rw [hii, hi x, hinner]
      refine sum_congr rfl fun j _ => ?_
      rw [RCLike.conj_mul]
      exact (Complex.ofReal_pow _ 2).symm
    rw [hni x] at h1
    have h1' : ((∑ j : Fin k, ‖a x j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simpa using h1.symm
    exact Complex.ofReal_inj.mp h1'

  have hprod_eq : ∑ x : Fin N, ∑ j : Fin k, ‖a x j‖ * ‖⟪e x, v j⟫‖
      = ∑ p : Fin N × Fin k, ‖a p.1 p.2‖ * ‖⟪e p.1, v p.2⟫‖ := by
    rw [← Finset.univ_product_univ (α := Fin N) (β := Fin k)]
    rw [Finset.sum_product]
  rw [hprod_eq] at hsum_le

  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin N × Fin k))
    (fun p : Fin N × Fin k => ‖a p.1 p.2‖)
    (fun p : Fin N × Fin k => ‖⟪e p.1, v p.2⟫‖)

  have ha_sq : ∑ p : Fin N × Fin k, ‖a p.1 p.2‖ ^ 2 = (N : ℝ) := by
    rw [← Finset.univ_product_univ (α := Fin N) (β := Fin k)]
    rw [Finset.sum_product]
    calc ∑ x : Fin N, ∑ j : Fin k, ‖a x j‖ ^ 2 = ∑ _x : Fin N, (1 : ℝ) :=
          sum_congr rfl fun x _ => ha_norm x
      _ = (N : ℝ) := by simp

  have hg_sq : ∑ p : Fin N × Fin k, ‖⟪e p.1, v p.2⟫‖ ^ 2 ≤ (k : ℝ) := by
    rw [← Finset.univ_product_univ (α := Fin N) (β := Fin k)]
    rw [Finset.sum_product]
    calc ∑ x : Fin N, ∑ j : Fin k, ‖⟪e x, v j⟫‖ ^ 2
        = ∑ j : Fin k, ∑ x : Fin N, ‖⟪e x, v j⟫‖ ^ 2 := Finset.sum_comm
      _ ≤ ∑ j : Fin k, ‖v j‖ ^ 2 := by
          refine sum_le_sum fun j _ => ?_
          simpa using he.sum_inner_products_le (x := v j) (s := (Finset.univ : Finset (Fin N)))
      _ = ∑ _j : Fin k, (1 : ℝ) := by
          refine sum_congr rfl fun j _ => ?_
          rw [hv.1 j, one_pow]
      _ = (k : ℝ) := by simp

  have hsqrtN : Real.sqrt (∑ p : Fin N × Fin k, ‖a p.1 p.2‖ ^ 2) = Real.sqrt (N : ℝ) := by
    rw [ha_sq]
  have hsqrtk_le : Real.sqrt (∑ p : Fin N × Fin k, ‖⟪e p.1, v p.2⟫‖ ^ 2)
      ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hg_sq
  have hstep : ∑ p : Fin N × Fin k, ‖a p.1 p.2‖ * ‖⟪e p.1, v p.2⟫‖
      ≤ Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) := by
    calc ∑ p : Fin N × Fin k, ‖a p.1 p.2‖ * ‖⟪e p.1, v p.2⟫‖
        ≤ Real.sqrt (∑ p : Fin N × Fin k, ‖a p.1 p.2‖ ^ 2)
            * Real.sqrt (∑ p : Fin N × Fin k, ‖⟪e p.1, v p.2⟫‖ ^ 2) := hcs
      _ = Real.sqrt (N : ℝ)
            * Real.sqrt (∑ p : Fin N × Fin k, ‖⟪e p.1, v p.2⟫‖ ^ 2) := by rw [hsqrtN]
      _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtk_le (Real.sqrt_nonneg _)
  calc ∑ x : Fin N, ‖⟪e x, i x⟫‖
      ≤ ∑ p : Fin N × Fin k, ‖a p.1 p.2‖ * ‖⟪e p.1, v p.2⟫‖ := hsum_le
    _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ) := hstep
    _ = Real.sqrt ((N : ℝ) * (k : ℝ)) := (Real.sqrt_mul (Nat.cast_nonneg N) _).symm

/-- For `b ∈ [0, 1]` and unit vector families with `e x` orthogonal to `u x`, the sum of squared
distances from `Real.sqrt b • e x + Real.sqrt (1 - b) • u x` to `i x` is at least `2 * N *
(1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b * ∑ x, ‖⟪e x, i x⟫‖`
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem eq10_lower_bound
    (N : ℕ) (e u i : Fin N → V) (b : ℝ)
    (he : ∀ x, ‖e x‖ = 1)
    (hu_orth : ∀ x, ⟪e x, u x⟫ = 0)
    (hu : ∀ x, ‖u x‖ = 1)
    (hi : ∀ x, ‖i x‖ = 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    2 * (N : ℝ) * (1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b * (∑ x, ‖⟪e x, i x⟫‖)
      ≤ ∑ x : Fin N, ‖(Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x - i x‖ ^ 2 := by
  have h1b : 0 ≤ 1 - b := by linarith
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hs1b : 0 ≤ Real.sqrt (1 - b) := Real.sqrt_nonneg _
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hsq1b : Real.sqrt (1 - b) ^ 2 = 1 - b := Real.sq_sqrt h1b

  have hpoint : ∀ x : Fin N,
      2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ - 2 * Real.sqrt (1 - b)
        ≤ ‖(Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x - i x‖ ^ 2 := by
    intro x
    set p : V := (Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x with hpdef
    have hcross : ⟪(Real.sqrt b : ℂ) • e x, (Real.sqrt (1 - b) : ℂ) • u x⟫ = 0 := by
      rw [inner_smul_left, inner_smul_right, hu_orth x]
      simp
    have h1 : ‖(Real.sqrt b : ℂ) • e x‖ ^ 2 = b := by
      rw [norm_smul, he x, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsb,
        hsqb]
    have h2 : ‖(Real.sqrt (1 - b) : ℂ) • u x‖ ^ 2 = 1 - b := by
      rw [norm_smul, hu x, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs1b,
        hsq1b]
    have hp_norm : ‖p‖ ^ 2 = 1 := by
      rw [hpdef, norm_add_sq (𝕜 := ℂ), hcross, h1, h2]
      simp
    have hexp : ‖p - i x‖ ^ 2 = ‖p‖ ^ 2 - 2 * (⟪p, i x⟫).re + ‖i x‖ ^ 2 :=
      norm_sub_sq (𝕜 := ℂ) p (i x)
    have hre : (⟪p, i x⟫).re
        ≤ Real.sqrt b * ‖⟪e x, i x⟫‖ + Real.sqrt (1 - b) * ‖⟪u x, i x⟫‖ := by
      have hnorm : ‖⟪p, i x⟫‖
          ≤ Real.sqrt b * ‖⟪e x, i x⟫‖ + Real.sqrt (1 - b) * ‖⟪u x, i x⟫‖ := by
        rw [hpdef, inner_add_left, inner_smul_left, inner_smul_left]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul]
        have hcb : ‖(starRingEnd ℂ) ((Real.sqrt b : ℂ))‖ = Real.sqrt b := by
          rw [Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsb]
        have hc1b : ‖(starRingEnd ℂ) ((Real.sqrt (1 - b) : ℂ))‖ = Real.sqrt (1 - b) := by
          rw [Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs1b]
        rw [hcb, hc1b]
      exact le_trans (Complex.re_le_norm _) hnorm
    have hiu : ‖⟪u x, i x⟫‖ ≤ 1 := by
      calc ‖⟪u x, i x⟫‖ ≤ ‖u x‖ * ‖i x‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [hu x, hi x, one_mul]
    rw [hexp, hp_norm, hi x]
    nlinarith [hre, hiu, hsb, hs1b]

  have hsum_point :
      ∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ - 2 * Real.sqrt (1 - b))
        ≤ ∑ x : Fin N,
            ‖(Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x - i x‖ ^ 2 :=
    sum_le_sum fun x _ => hpoint x

  have hconst : ∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ - 2 * Real.sqrt (1 - b))
      = 2 * (N : ℝ) - 2 * Real.sqrt b * (∑ x, ‖⟪e x, i x⟫‖)
        - 2 * Real.sqrt (1 - b) * (N : ℝ) := by
    have hsplit1 : ∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ - 2 * Real.sqrt (1 - b))
        = (∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖))
          - ∑ _x : Fin N, 2 * Real.sqrt (1 - b) := by
      simp only [Finset.sum_sub_distrib]
    rw [hsplit1]
    have hsplit2 : ∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖)
        = (∑ _x : Fin N, (2 : ℝ)) - ∑ x : Fin N, 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ := by
      simp only [Finset.sum_sub_distrib]
    rw [hsplit2]
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  calc 2 * (N : ℝ) * (1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b * (∑ x, ‖⟪e x, i x⟫‖)
      = 2 * (N : ℝ) - 2 * Real.sqrt b * (∑ x, ‖⟪e x, i x⟫‖)
        - 2 * Real.sqrt (1 - b) * (N : ℝ) := by ring
    _ = ∑ x : Fin N, (2 - 2 * Real.sqrt b * ‖⟪e x, i x⟫‖ - 2 * Real.sqrt (1 - b)) :=
        hconst.symm
    _ ≤ ∑ x : Fin N,
          ‖(Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x - i x‖ ^ 2 := hsum_point

/-- Under the unit-vector and orthogonality hypotheses, an overlap-sum bound `Real.sqrt (N * k)`
gives the squared-distance lower bound `2 * N * (1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b *
Real.sqrt (N * k)` for `b ∈ [0, 1]` [FarhiGoldstoneGutmannNagaj2008]. -/
theorem eq10_lower_bound_with_sqrt
    (N k : ℕ) (e u i : Fin N → V) (b : ℝ)
    (he : ∀ x, ‖e x‖ = 1)
    (hu_orth : ∀ x, ⟪e x, u x⟫ = 0)
    (hu : ∀ x, ‖u x‖ = 1)
    (hi : ∀ x, ‖i x‖ = 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hbound : ∑ x : Fin N, ‖⟪e x, i x⟫‖ ≤ Real.sqrt ((N : ℝ) * (k : ℝ))) :
    2 * (N : ℝ) * (1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b * Real.sqrt ((N : ℝ) * (k : ℝ))
      ≤ ∑ x : Fin N,
          ‖(Real.sqrt b : ℂ) • e x + (Real.sqrt (1 - b) : ℂ) • u x - i x‖ ^ 2 := by
  have hbase := eq10_lower_bound N e u i b he hu_orth hu hi hb0 hb1
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt b)
  linarith [hbase, hmul]

/-- For nonnegative `T`, if `S T = 0`, the derivative exists and is interval integrable, and
`|deriv S t| ≤ 2 * E * (1 - t / T) * K` on the interval, then `S 0 ≤ E * T * K`
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem deriv_abs_integral_bound
    (S : ℝ → ℝ) (E T K : ℝ) (hT : 0 ≤ T)
    (hST : S T = 0)
    (hderiv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt S (deriv S t) t)
    (hint_deriv : IntervalIntegrable (fun t => deriv S t) volume 0 T)
    (hbound : ∀ t ∈ Set.uIcc 0 T, |deriv S t| ≤ 2 * E * (1 - t / T) * K) :
    S 0 ≤ E * T * K := by
  have hdiff : ∀ x ∈ Set.uIcc 0 T, DifferentiableAt ℝ S x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hFTC : ∫ t in (0 : ℝ)..T, deriv S t = S T - S 0 :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint_deriv
  have hint_abs : IntervalIntegrable (fun t => |deriv S t|) volume 0 T :=
    hint_deriv.abs
  have hcont_b : Continuous fun t : ℝ => 2 * E * (1 - t / T) * K := by fun_prop
  have hint_b : IntervalIntegrable (fun t => 2 * E * (1 - t / T) * K) volume 0 T :=
    hcont_b.intervalIntegrable 0 T
  have huIcc : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT

  have hkey : S 0 ≤ ∫ t in (0 : ℝ)..T, |deriv S t| := by
    have h2 : S 0 - S T = ∫ t in (0 : ℝ)..T, -deriv S t := by
      rw [intervalIntegral.integral_neg, hFTC]; ring
    have h3 : S 0 - S T ≤ ∫ t in (0 : ℝ)..T, |deriv S t| := by
      rw [h2]
      exact intervalIntegral.integral_mono_on hT hint_deriv.neg hint_abs
        (fun t _ => neg_le_abs (deriv S t))
    calc S 0 = (S 0 - S T) + S T := by ring
      _ = S 0 - S T := by rw [hST, add_zero]
      _ ≤ ∫ t in (0 : ℝ)..T, |deriv S t| := h3

  have hmono : ∫ t in (0 : ℝ)..T, |deriv S t|
      ≤ ∫ t in (0 : ℝ)..T, 2 * E * (1 - t / T) * K := by
    refine intervalIntegral.integral_mono_on hT hint_abs hint_b (fun t ht => ?_)
    rw [← huIcc] at ht
    exact hbound t ht
  have hvalue : ∫ t in (0 : ℝ)..T, 2 * E * (1 - t / T) * K = E * T * K := by
    rcases eq_or_lt_of_le hT with hT0 | hTpos
    · subst hT0; simp
    · have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
      have hanti : ∀ t ∈ Set.uIcc (0 : ℝ) T,
          HasDerivAt (fun t : ℝ => 2 * E * K * (t - t ^ 2 / (2 * T)))
            (2 * E * (1 - t / T) * K) t := by
        intro t _
        have hpow : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * T)) (2 * t / (2 * T)) t := by
          have := (hasDerivAt_pow 2 t).div_const (2 * T)
          simpa [pow_two] using this
        have hbase : HasDerivAt (fun t : ℝ => t - t ^ 2 / (2 * T)) (1 - 2 * t / (2 * T)) t :=
          (hasDerivAt_id t).sub hpow
        have h2 : HasDerivAt (fun t : ℝ => 2 * E * K * (t - t ^ 2 / (2 * T)))
            (2 * E * K * (1 - 2 * t / (2 * T))) t := hbase.const_mul (2 * E * K)
        exact h2.congr_deriv (by field_simp; try ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hanti hint_b]
      have hcalc : (fun t : ℝ => 2 * E * K * (t - t ^ 2 / (2 * T))) T
            - (fun t : ℝ => 2 * E * K * (t - t ^ 2 / (2 * T))) 0 = E * T * K := by
        simp only
        field_simp [hTne]
        ring
      simpa using hcalc
  calc S 0 ≤ ∫ t in (0 : ℝ)..T, |deriv S t| := hkey
    _ ≤ ∫ t in (0 : ℝ)..T, 2 * E * (1 - t / T) * K := hmono
    _ = E * T * K := hvalue

end Qatlib.Papers.AdiabaticFail05.MainResults
