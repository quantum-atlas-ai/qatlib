/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HidShiftQuad09.MainResults.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Correlation and success perturbation near quadratics

This module proves correlation and Euclidean-vector estimates used in the close-quadratic
analysis of [Roetteler2009]. Large absolute correlation gives either a small disagreement
fraction or a disagreement fraction close to one.

The success estimates compare squared overlaps of nearby vectors. Under the explicitly supplied
unit-vector model and correlation-power identity, `source_theorem2_findCloseQuadratic` gives a
lower bound by a positive multiple of `1 - n * ε`.

## Main statements

* `abs_corr_gt_implies_close`: translates absolute correlation into a disagreement alternative.
* `success_perturbation`: bounds the change in a squared success overlap.
* `source_theorem2_findCloseQuadratic`: combines the correlation and perturbation hypotheses.

## References

* [Roetteler, 2009][Roetteler2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.FindCloseQuadratic

open scoped BigOperators RealInnerProductSpace
open Qatlib.Papers.HidShiftQuad09.MainResults.Defs

/-- If the absolute correlation is greater than `1 - ε`, the disagreement fraction is less than
`ε / 2` or greater than `1 - ε / 2`. [Roetteler2009]. -/
theorem abs_corr_gt_implies_close {n : ℕ} (f g : Cube n → ZMod 2) (ε : ℝ)
    (h : 1 - ε < |corr f g|) :
    disagreeFrac f g < ε / 2 ∨ 1 - ε / 2 < disagreeFrac f g := by
  rw [corr_eq_one_sub_two_disagree] at h
  set d : ℝ := disagreeFrac f g with hd
  have hb := disagreeFrac_bounds f g
  rcases lt_abs.mp h with hpos | hneg
  · left
    linarith
  · right
    linarith

/-- For nonnegative `r` and `ε` with `1 - ε ≤ r`, the natural power `r ^ k` is at least `1 - k *
ε`. [Roetteler2009]. -/
theorem one_sub_mul_le_pow_abs (k : ℕ) {r ε : ℝ}
    (_hε0 : 0 ≤ ε) (hr0 : 0 ≤ r) (hr : 1 - ε ≤ r) :
    1 - (k : ℝ) * ε ≤ r ^ k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp
  · by_cases hε1 : ε ≤ 1
    · have hb : 1 - (k : ℝ) * ε ≤ (1 - ε) ^ k := bernstein_pow k ε hε1
      have hmono : (1 - ε) ^ k ≤ r ^ k :=
        pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 - ε) hr k
      linarith
    · push Not at hε1
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have : 1 - (k : ℝ) * ε ≤ 0 := by nlinarith
      have : 0 ≤ r ^ k := pow_nonneg hr0 k
      linarith

/-- The squared distance between two unit vectors in a real Euclidean space equals two minus
twice their inner product. -/
theorem norm_sub_sq_unit {N : ℕ} (u v : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫ := by
  rw [norm_sub_sq_real, hu, hv]
  ring

/-- If unit vectors `ψg` and `φ` have squared inner product at least one half and `ψf` is within
distance `d` of `ψg`, then its squared inner product with `φ` is at least `1 / 2 - 2 * d`.
[Roetteler2009]. -/
theorem success_perturbation {N : ℕ} (ψf ψg φ : EuclideanSpace ℝ (Fin N))
    (hψg : ‖ψg‖ = 1) (hφ : ‖φ‖ = 1)
    (hp0 : 1 / 2 ≤ ⟪ψg, φ⟫ ^ 2)
    (d : ℝ) (hd : ‖ψf - ψg‖ ≤ d) :
    1 / 2 - 2 * d ≤ ⟪ψf, φ⟫ ^ 2 := by
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hd
  set a : ℝ := ⟪ψg, φ⟫ with ha
  set b : ℝ := ⟪ψf, φ⟫ - a with hb
  have hbf : b = ⟪ψf - ψg, φ⟫ := by
    rw [hb, ha, inner_sub_left]
  have hb_abs : |b| ≤ d := by
    have h1 : |b| ≤ ‖ψf - ψg‖ * ‖φ‖ := by
      rw [hbf, real_inner_comm]
      calc |⟪φ, ψf - ψg⟫| ≤ ‖φ‖ * ‖ψf - ψg‖ := abs_real_inner_le_norm φ (ψf - ψg)
        _ = ‖ψf - ψg‖ * ‖φ‖ := mul_comm _ _
    rw [hφ, mul_one] at h1
    exact le_trans h1 hd
  have ha_abs : |a| ≤ 1 := by
    have h1 : |a| ≤ ‖ψg‖ * ‖φ‖ := by
      rw [ha, real_inner_comm]
      calc |⟪φ, ψg⟫| ≤ ‖φ‖ * ‖ψg‖ := abs_real_inner_le_norm φ ψg
        _ = ‖ψg‖ * ‖φ‖ := mul_comm _ _
    rwa [hψg, hφ, mul_one] at h1
  have hin : ⟪ψf, φ⟫ = a + b := by rw [hb]; ring
  rw [hin]
  have hmul : |a * b| ≤ d := by
    rw [abs_mul]
    calc |a| * |b| ≤ 1 * d := by
          exact mul_le_mul ha_abs hb_abs (abs_nonneg _) (by linarith)
      _ = d := one_mul d
  have hab : -d ≤ a * b := (abs_le.mp hmul).1
  have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
  nlinarith [hab, hp0, hb2]

/-- For `ε ≥ 0` and `k ≤ n / 1000`, the perturbation bound `1 / 2 - 2 * sqrt (2 * k * ε)` is at
least `(1 / 8) * (1 - n * ε)`. [Roetteler2009]. -/
theorem corr_perturbation_numeric (n k : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hk : (k : ℝ) ≤ (n : ℝ) / 1000) :
    (1 / 8 : ℝ) * (1 - (n : ℝ) * ε) ≤ 1 / 2 - 2 * Real.sqrt (2 * (k : ℝ) * ε) := by
  set T : ℝ := (n : ℝ) * ε with hT
  have hT0 : 0 ≤ T := by positivity
  have h2k : 2 * (k : ℝ) * ε ≤ T / 500 := by
    have : 2 * (k : ℝ) * ε ≤ 2 * ((n : ℝ) / 1000) * ε := by nlinarith [hε0]
    rw [hT]; nlinarith
  by_cases h6 : T ≤ 6
  · have hsqrt_le : Real.sqrt (2 * (k : ℝ) * ε) ≤ Real.sqrt (6 / 500) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have hs : Real.sqrt (6 / 500) ≤ (0.142 : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    have hR : (1 / 8 : ℝ) * (1 - T) ≤ 1 / 8 := by nlinarith
    have hL : (1 / 8 : ℝ) ≤ 1 / 2 - 2 * Real.sqrt (6 / 500) := by nlinarith
    nlinarith
  · push Not at h6
    have ham : 2 * Real.sqrt (T / 500) ≤ T / 500 + 1 := by
      have hx : 0 ≤ T / 500 := by positivity
      nlinarith [sq_nonneg (Real.sqrt (T / 500) - 1), Real.sq_sqrt hx]
    have hsqrt_le : Real.sqrt (2 * (k : ℝ) * ε) ≤ Real.sqrt (T / 500) := by
      apply Real.sqrt_le_sqrt; exact h2k
    have h2 : 2 * Real.sqrt (2 * (k : ℝ) * ε) ≤ T / 500 + 1 := by nlinarith
    nlinarith

/-- Given the stated high correlation with a quadratic polynomial and unit-vector overlap model,
there is a positive constant `c` such that the squared success overlap is at least `c * (1 -
n * ε)`. [Roetteler2009]. -/
theorem source_theorem2_findCloseQuadratic
    (n : ℕ) (_hn : 0 < n) (ε : ℝ) (f : Cube n → ZMod 2) (g : QuadPoly n)
    (hε0 : 0 ≤ ε)
    (hcorr : 1 - ε < |corr f g.eval|)
    {N : ℕ} (ψf ψg φ : EuclideanSpace ℝ (Fin N))
    (hψf : ‖ψf‖ = 1) (hψg : ‖ψg‖ = 1) (hφ : ‖φ‖ = 1)
    (hinner : ⟪ψf, ψg⟫ = |corr f g.eval| ^ (n / 1000))
    (hp0 : 1 / 2 ≤ ⟪ψg, φ⟫ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ c * (1 - (n : ℝ) * ε) ≤ ⟪ψf, φ⟫ ^ 2 := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  set r : ℝ := |corr f g.eval| with hr
  have hr0 : 0 ≤ r := abs_nonneg _
  have hr1 : r ≤ 1 := abs_corr_le_one f g.eval
  have hrge : 1 - ε ≤ r := le_of_lt hcorr

  have hk : ((n / 1000 : ℕ) : ℝ) ≤ (n : ℝ) / 1000 := Nat.cast_div_le
  have hkeps : 1 - ((n / 1000 : ℕ) : ℝ) * ε ≤ r ^ (n / 1000) :=
    one_sub_mul_le_pow_abs (n / 1000) hε0 hr0 hrge

  have hinner' : ⟪ψf, ψg⟫ = r ^ (n / 1000) := hinner
  have hnorm : ‖ψf - ψg‖ ^ 2 = 2 - 2 * r ^ (n / 1000) := by
    rw [norm_sub_sq_unit ψf ψg hψf hψg, hinner']
  have hsq : ‖ψf - ψg‖ ^ 2 ≤ 2 * ((n / 1000 : ℕ) : ℝ) * ε := by
    rw [hnorm]; nlinarith
  have hdist : ‖ψf - ψg‖ ≤ Real.sqrt (2 * ((n / 1000 : ℕ) : ℝ) * ε) :=
    Real.le_sqrt_of_sq_le hsq
  have hpert := success_perturbation ψf ψg φ hψg hφ hp0
    (Real.sqrt (2 * ((n / 1000 : ℕ) : ℝ) * ε)) hdist

  have hnum := corr_perturbation_numeric n (n / 1000) ε hε0 hk
  linarith

end Qatlib.Papers.HidShiftQuad09.MainResults.FindCloseQuadratic
