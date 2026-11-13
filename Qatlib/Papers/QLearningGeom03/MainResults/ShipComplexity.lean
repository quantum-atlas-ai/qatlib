/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebraAbs
import Qatlib.Papers.QLearningGeom03.MainResults.AmplitudeAmplification
import Qatlib.Papers.QLearningGeom03.MainResults.ShipSine

/-!
# Spectral and query bounds for battleship learning

This module derives sine formulas for the eigenvalues of the normalized battleship matrix and
estimates their mean absolute value `bsS`. It proves an explicit O(√N) amplification query bound
when 4(2r + 1) ≤ N and a lower bound proportional to √N/(1 + log N) for amplification reaching
success probability at least 1/2 under the stated size assumptions.

The final results characterize equivalence of battleship value oracles by two boundary queries.
These statements develop the battleship analysis of [HunzikerEtAl2003].

## Main statements

* `smallship_queries`: An explicit upper bound proportional to √N.
* `bsS_le`: An upper bound on the mean absolute eigenvalue.
* `bigship_queries_lower`: A lower bound for amplification achieving success at least 1/2.
* `equiv_oracle_iff`: Two boundary values characterize equivalence of value oracles.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

/-- The normalized battleship phase coefficient vector `epsBS r` divided by √N. -/
noncomputable def bsCoeff (r : ℕ) : ZMod N → ℂ :=
  fun k => (((Real.sqrt N : ℝ) : ℂ))⁻¹ * epsBS (N := N) r k

/-- A Fourier eigenvalue of `bsCoeff r` is 1/√N times the corresponding Fourier coefficient of
the unnormalized battleship phase. -/
lemma eigen_bsCoeff (r : ℕ) (j : ZMod N) :
    eigen (bsCoeff (N := N) r) j
      = (((Real.sqrt N : ℝ) : ℂ))⁻¹
          * (∑ x : ZMod N, epsBS (N := N) r x * chiN j x) := by
  unfold eigen bsCoeff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- A nonzero cyclic frequency gives a positive angle π j/N. -/
lemma bs_theta_pos {j : ZMod N} (hj : j ≠ 0) :
    0 < Real.pi * (j.val : ℝ) / (N : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hjval : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
  positivity

/-- The angle π j/N associated with a cyclic frequency is strictly less than π. -/
lemma bs_theta_lt_pi (j : ZMod N) :
    Real.pi * (j.val : ℝ) / (N : ℝ) < Real.pi := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlt : (j.val : ℝ) < N := by exact_mod_cast ZMod.val_lt j
  calc Real.pi * (j.val : ℝ) / (N : ℝ) < Real.pi * (N : ℝ) / (N : ℝ) := by
        apply div_lt_div_of_pos_right _ hN
        exact mul_lt_mul_of_pos_left hlt Real.pi_pos
    _ = Real.pi := by field_simp

/-- The sine of π j/N is nonzero at a nonzero cyclic frequency. -/
lemma bs_theta_sin_ne_zero {j : ZMod N} (hj : j ≠ 0) :
    Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) ≠ 0 := by
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (bs_theta_pos hj) (bs_theta_lt_pi j))

/-- For 2r + 1 ≤ N and j ≠ 0, the normalized battleship eigenvalue is -2/√N times sin((2r +
1)πj/N)/sin(πj/N), as used in [Hunziker et al., Theorem 6.1][HunzikerEtAl2003]. -/
theorem bs_eigenvalue_sine {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0) :
    eigen (bsCoeff (N := N) r) j
      = -(((Real.sqrt N : ℝ) : ℂ))⁻¹ * 2
          * ((Real.sin (((2 * r + 1 : ℕ) : ℝ)
                * (Real.pi * (j.val : ℝ) / (N : ℝ)))
              / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
  rw [eigen_bsCoeff, bs_eigenvalue, ite_eq_right hj, bs_window_sine h hj (bs_theta_sin_ne_zero hj)]
  ring

/-- If 2r + 1 ≤ N, the zero-frequency battleship eigenvalue is (N - 2(2r + 1))/√N. -/
theorem bs_eigenvalue_zero {r : ℕ} (h : 2 * r + 1 ≤ N) :
    eigen (bsCoeff (N := N) r) 0
      = ((((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N : ℝ) : ℂ) := by
  rw [eigen_bsCoeff, bs_lambda_zero h]
  rw [show (((Real.sqrt N : ℝ) : ℂ))⁻¹ * (((N : ℂ)) - 2 * (((2 * r + 1 : ℕ)) : ℂ))
        = ((((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N : ℝ) : ℂ) from by
    push_cast
    ring]

/-- If 2(2r + 1) ≤ N, the absolute zero-frequency battleship eigenvalue is (N - 2(2r + 1))/√N,
as used in [HunzikerEtAl2003]. -/
theorem absEigen_bs_zero {r : ℕ} (h : 2 * (2 * r + 1) ≤ N) :
    absEigen (bsCoeff (N := N) r) 0
      = ((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd : 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h' : ((2 * (2 * r + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    push_cast at h'
    push_cast
    linarith
  have hnonneg : 0 ≤ ((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    linarith
  unfold absEigen
  rw [bs_eigenvalue_zero (by omega), Complex.norm_real, Real.norm_of_nonneg hnonneg]

/-- At a nonzero frequency and for 2r + 1 ≤ N, the absolute battleship eigenvalue is 2/√N times
the absolute sine quotient, as used in [HunzikerEtAl2003]. -/
theorem absEigen_bs_sine {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0) :
    absEigen (bsCoeff (N := N) r) j
      = (2 / Real.sqrt N)
          * |Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
              / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ))| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  unfold absEigen
  rw [bs_eigenvalue_sine h hj]
  rw [show -(((Real.sqrt N : ℝ) : ℂ))⁻¹ * 2
        * ((Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
            / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ)
      = ((-(2 / Real.sqrt N)
          * (Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
              / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ))) : ℝ) : ℂ) from by
    push_cast
    ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.sqrt N)]

/-- The mean of the absolute Fourier eigenvalues of the normalized battleship coefficient
vector. -/
noncomputable def bsS (r : ℕ) : ℝ :=
  ((N : ℝ))⁻¹ * ∑ j : ZMod N, absEigen (bsCoeff (N := N) r) j

/-- The mean absolute battleship eigenvalue is nonnegative. -/
lemma bsS_nonneg (r : ℕ) : 0 ≤ bsS (N := N) r := by
  unfold bsS
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun j _ => absEigen_nonneg _ _

/-- The common diagonal entry at zero of the battleship spectral absolute-value matrix is the
complex embedding of `bsS r`. -/
theorem absGroupAlgebra_diag_bs (r : ℕ) :
    absGroupAlgebra (bsCoeff (N := N) r) 0 0 = ((bsS (N := N) r : ℝ) : ℂ) := by
  rw [absGroupAlgebra_diag]
  unfold bsS
  push_cast
  ring

/-- If 4(2r + 1) ≤ N, the mean absolute battleship eigenvalue is at least 1/(2√N), as used in
[Hunziker et al., Theorem 6.1][HunzikerEtAl2003]. -/
theorem bsS_ge {r : ℕ} (h : 4 * (2 * r + 1) ≤ N) :
    (2 * Real.sqrt N)⁻¹ ≤ bsS (N := N) r := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hR : (4 : ℝ) * ((2 * r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h' : ((4 * (2 * r + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    push_cast at h'
    push_cast
    linarith
  have hsingle : absEigen (bsCoeff (N := N) r) 0
      ≤ ∑ j : ZMod N, absEigen (bsCoeff (N := N) r) j :=
    Finset.single_le_sum (f := fun j => absEigen (bsCoeff (N := N) r) j)
      (fun j _ => absEigen_nonneg _ _) (Finset.mem_univ 0)
  have hNd : (N : ℝ) / 2 ≤ (N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ) := by linarith
  have hterm : (2 * Real.sqrt N)⁻¹
      ≤ ((N : ℝ))⁻¹ * absEigen (bsCoeff (N := N) r) 0 := by
    rw [absEigen_bs_zero (by omega)]
    have hfrac : (2 * Real.sqrt N)⁻¹
        = ((N : ℝ) / 2) / ((N : ℝ) * Real.sqrt N) := by
      field_simp
    have hNN : (0 : ℝ) < (N : ℝ) * Real.sqrt N := by positivity
    calc (2 * Real.sqrt N)⁻¹
        = ((N : ℝ) / 2) / ((N : ℝ) * Real.sqrt N) := hfrac
      _ ≤ ((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / ((N : ℝ) * Real.sqrt N) :=
          div_le_div_of_nonneg_right hNd (le_of_lt hNN)
      _ = ((N : ℝ))⁻¹
            * (((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N) := by
          field_simp
  calc (2 * Real.sqrt N)⁻¹
      ≤ ((N : ℝ))⁻¹ * absEigen (bsCoeff (N := N) r) 0 := hterm
    _ ≤ ((N : ℝ))⁻¹ * ∑ j : ZMod N, absEigen (bsCoeff (N := N) r) j :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
    _ = bsS (N := N) r := rfl

/-- The amplification angle given by arcsin of the minimum of `bsS r` and 1. -/
noncomputable def bsTheta (r : ℕ) : ℝ := Real.arcsin (min (bsS (N := N) r) 1)

/-- If 4(2r + 1) ≤ N, the chosen amplification query count is at most 2(π/2 + 1)√N. This gives
the upper bound associated with [Hunziker et al., Theorem 6.1][HunzikerEtAl2003]. -/
theorem smallship_queries {r : ℕ} (h : 4 * (2 * r + 1) ≤ N) :
    2 * amplIters (bsTheta (N := N) r) + 1 ≤ 2 * (Real.pi / 2 + 1) * Real.sqrt N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsge : (2 * Real.sqrt N)⁻¹ ≤ bsS (N := N) r := bsS_ge h
  have hspos : 0 < bsS (N := N) r := lt_of_lt_of_le (by positivity) hsge
  set s := bsS (N := N) r with hs_def
  have hminpos : 0 < min s 1 := lt_min hspos one_pos
  have hminle : min s 1 ≤ 1 := min_le_right _ _
  have hsin : Real.sin (bsTheta (N := N) r) = min s 1 :=
    Real.sin_arcsin (by linarith [le_of_lt hminpos]) hminle
  have hθ0 : 0 < bsTheta (N := N) r := Real.arcsin_pos.mpr hminpos
  have hθ2 : bsTheta (N := N) r ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hbound := amplified_query_bound hminpos hminle hsin hθ0 hθ2
  rcases le_or_gt s 1 with hs1 | hs1
  · have hmin : min s 1 = s := min_eq_left hs1
    rw [hmin] at hbound
    have hinv : (1 : ℝ) / s ≤ 2 * Real.sqrt N := by
      rw [div_le_iff₀ hspos]
      calc (1 : ℝ) = (2 * Real.sqrt N) * (2 * Real.sqrt N)⁻¹ :=
            (mul_inv_cancel₀ (by positivity)).symm
        _ ≤ (2 * Real.sqrt N) * s :=
            mul_le_mul_of_nonneg_left hsge (by positivity)
    have hhalf : (Real.pi / 2 + 1) / s ≤ 2 * (Real.pi / 2 + 1) * Real.sqrt N := by
      rw [div_eq_mul_inv]
      calc (Real.pi / 2 + 1) * s⁻¹
          ≤ (Real.pi / 2 + 1) * (2 * Real.sqrt N) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simpa [one_div] using hinv
        _ = 2 * (Real.pi / 2 + 1) * Real.sqrt N := by ring
    linarith
  · have hmin : min s 1 = 1 := min_eq_right (le_of_lt hs1)
    rw [hmin] at hbound
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    have hle : (Real.pi / 2 + 1) / 1 ≤ 2 * (Real.pi / 2 + 1) * Real.sqrt N := by
      have hpi : 0 ≤ Real.pi / 2 + 1 := by positivity
      nlinarith
    linarith

/-- The reciprocal of sin(πj/N), used to bound the nonzero battleship eigenvalues. -/
noncomputable def bsCsc (j : ℕ) : ℝ :=
  (Real.sin (Real.pi * (j : ℝ) / (N : ℝ)))⁻¹

/-- For 1 ≤ j < N, sin(πj/N) is at least 2 min(j, N - j)/N. -/
lemma sin_bs_ge {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N) :
    2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ)
      ≤ Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rcases le_or_gt (2 * j) N with h2j | h2j
  · have hmin : min j (N - j) = j := Nat.min_eq_left (by omega)
    have hx0 : 0 ≤ Real.pi * (j : ℝ) / (N : ℝ) := by positivity
    have hx2 : Real.pi * (j : ℝ) / (N : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hN]
      have h2jR : 2 * (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2j
      nlinarith [Real.pi_pos]
    have hjordan := Real.mul_le_sin hx0 hx2
    calc 2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ)
        = 2 / Real.pi * (Real.pi * (j : ℝ) / (N : ℝ)) := by
          rw [hmin]
          field_simp
      _ ≤ Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) := hjordan
  · have hmin : min j (N - j) = N - j := Nat.min_eq_right (by omega)
    have h2y : 2 * (N - j) ≤ N := by omega
    have hβ0 : 0 ≤ Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ) := by positivity
    have hβ2 : Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hN]
      have h2yR : 2 * ((N - j : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2y
      nlinarith [Real.pi_pos]
    have hjordan := Real.mul_le_sin hβ0 hβ2
    have harg : Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ)
        = Real.pi - Real.pi * (j : ℝ) / (N : ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ N)]
      field_simp
    rw [harg, Real.sin_pi_sub] at hjordan
    calc 2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ)
        = 2 / Real.pi * (Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ)) := by
          rw [hmin]
          field_simp
      _ = 2 / Real.pi * (Real.pi - Real.pi * (j : ℝ) / (N : ℝ)) := by rw [harg]
      _ ≤ Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) := hjordan

/-- For 1 ≤ j < N, `bsCsc j` is bounded by N/2 times the sum of the reciprocals of j and N - j. -/
lemma csc_le_pair {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N) :
    bsCsc (N := N) j
      ≤ (N : ℝ) / 2 * ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hjpos : 0 < j := by omega
  have hNjpos : 0 < N - j := by omega
  have hminpos : (0 : ℝ) < ((min j (N - j) : ℕ) : ℝ) := by
    have : 0 < min j (N - j) := lt_min hjpos hNjpos
    exact_mod_cast this
  have hbpos : (0 : ℝ) < 2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ) := by positivity
  have hsinpos : (0 : ℝ) < Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) :=
    lt_of_lt_of_le hbpos (sin_bs_ge hj1 hjN)
  have hinv : bsCsc (N := N) j
      ≤ (2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ))⁻¹ := by
    unfold bsCsc
    exact (inv_le_inv₀ hsinpos hbpos).mpr (sin_bs_ge hj1 hjN)
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
  have hNjR : (0 : ℝ) < ((N - j : ℕ) : ℝ) := by exact_mod_cast hNjpos
  rcases le_or_gt j (N - j) with hle | hlt
  · have hmin : min j (N - j) = j := Nat.min_eq_left hle
    have hNjinv : (0 : ℝ) ≤ ((N - j : ℕ) : ℝ)⁻¹ := by positivity
    calc bsCsc (N := N) j
        ≤ (2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ))⁻¹ := hinv
      _ = (N : ℝ) / (2 * (j : ℝ)) := by
          rw [hmin]
          field_simp
      _ = (N : ℝ) / 2 * (j : ℝ)⁻¹ := by field_simp
      _ ≤ (N : ℝ) / 2 * ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  · have hmin : min j (N - j) = N - j := Nat.min_eq_right (le_of_lt hlt)
    have hJinv : (0 : ℝ) ≤ (j : ℝ)⁻¹ := by positivity
    calc bsCsc (N := N) j
        ≤ (2 * ((min j (N - j) : ℕ) : ℝ) / (N : ℝ))⁻¹ := hinv
      _ = (N : ℝ) / (2 * ((N - j : ℕ) : ℝ)) := by
          rw [hmin]
          field_simp
      _ = (N : ℝ) / 2 * ((N - j : ℕ) : ℝ)⁻¹ := by field_simp
      _ ≤ (N : ℝ) / 2 * ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

/-- For N ≥ 2, the sum of 1/j + 1/(N - j) over 1 ≤ j < N is at most 2(1 + log N). -/
lemma sum_pair_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) :
    ∑ j ∈ Finset.Ico 1 N, ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹)
      ≤ 2 * (1 + Real.log N) := by
  have hpred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos (by omega : 0 < N)
  have hS1 : ∑ j ∈ Finset.Ico 1 N, (j : ℝ)⁻¹
      = ((harmonic (N - 1) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc, ← Finset.Ico_add_one_right_eq_Icc, hpred]
    push_cast
    rfl
  have hS2 : ∑ j ∈ Finset.Ico 1 N, ((N - j : ℕ) : ℝ)⁻¹
      = ∑ j ∈ Finset.Ico 1 N, (j : ℝ)⁻¹ := by
    have h := Finset.sum_Ico_reflect (fun k : ℕ => ((k : ℝ))⁻¹) 1 (m := N) (n := N)
      (by omega : N ≤ N + 1)
    simpa using h
  have hlog : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (by omega : N - 1 ≠ 0)
    · exact_mod_cast Nat.sub_le N 1
  have hharm : ((harmonic (N - 1) : ℚ) : ℝ) ≤ 1 + Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log (N - 1)
    linarith
  calc ∑ j ∈ Finset.Ico 1 N, ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹)
      = (∑ j ∈ Finset.Ico 1 N, (j : ℝ)⁻¹)
          + ∑ j ∈ Finset.Ico 1 N, ((N - j : ℕ) : ℝ)⁻¹ := Finset.sum_add_distrib
    _ = 2 * ((harmonic (N - 1) : ℚ) : ℝ) := by rw [hS2, hS1]; ring
    _ ≤ 2 * (1 + Real.log N) := by linarith

/-- For N ≥ 2, the sum of `bsCsc j` over 1 ≤ j < N is at most N(1 + log N). -/
lemma bs_csc_sum_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) :
    ∑ j ∈ Finset.Ico 1 N, bsCsc (N := N) j ≤ (N : ℝ) * (1 + Real.log N) := by
  calc ∑ j ∈ Finset.Ico 1 N, bsCsc (N := N) j
      ≤ ∑ j ∈ Finset.Ico 1 N,
          (N : ℝ) / 2 * ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        exact csc_le_pair (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    _ = (N : ℝ) / 2
          * ∑ j ∈ Finset.Ico 1 N, ((j : ℝ)⁻¹ + ((N - j : ℕ) : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ (N : ℝ) / 2 * (2 * (1 + Real.log N)) := by
        apply mul_le_mul_of_nonneg_left (sum_pair_le hN2) (by positivity)
    _ = (N : ℝ) * (1 + Real.log N) := by ring

/-- For 2r + 1 ≤ N and j ≠ 0, the absolute battleship eigenvalue is at most 2/√N times `bsCsc
j.val`. -/
lemma absEigen_le_csc {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0) :
    absEigen (bsCoeff (N := N) r) j ≤ (2 / Real.sqrt N) * bsCsc (N := N) j.val := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hjval : 1 ≤ j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
  have hminpos : (0 : ℝ) < ((min j.val (N - j.val) : ℕ) : ℝ) := by
    have hjN : j.val < N := ZMod.val_lt j
    have hjvalpos : 0 < j.val := by omega
    have hNjpos : 0 < N - j.val := by omega
    have hpos : 0 < min j.val (N - j.val) := by
      rcases le_or_gt j.val (N - j.val) with hle | hlt
      · rwa [min_eq_left hle]
      · rwa [min_eq_right (le_of_lt hlt)]
    exact_mod_cast hpos
  have hbpos : (0 : ℝ) < 2 * ((min j.val (N - j.val) : ℕ) : ℝ) / (N : ℝ) := by
    positivity
  have hsinpos : 0 < Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) :=
    lt_of_lt_of_le hbpos (sin_bs_ge hjval (ZMod.val_lt j))
  rw [absEigen_bs_sine h hj]
  have hratio : |Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
        / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ))|
      ≤ (Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)))⁻¹ := by
    rw [abs_div, abs_of_pos hsinpos]
    have h1 : |Real.sin (((2 * r + 1 : ℕ) : ℝ)
          * (Real.pi * (j.val : ℝ) / (N : ℝ)))| ≤ 1 := Real.abs_sin_le_one _
    calc |Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))|
          / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ))
        ≤ 1 / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) :=
          div_le_div_of_nonneg_right h1 hsinpos.le
      _ = (Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)))⁻¹ := one_div _
  calc (2 / Real.sqrt N)
        * |Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
            / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ))|
      ≤ (2 / Real.sqrt N) * (Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (2 / Real.sqrt N) * bsCsc (N := N) j.val := rfl

/-- A sum over the nonzero residues of `ZMod N` equals the sum over the natural representatives
from 1 through N - 1. -/
lemma sum_erase_zero_eq {M : Type} [AddCommMonoid M] (f : ZMod N → M) :
    ∑ j ∈ Finset.univ.erase (0 : ZMod N), f j
      = ∑ k ∈ Finset.Ico 1 N, f ((k : ℕ) : ZMod N) := by
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    exact Finset.mem_Ico.mpr ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj0), ZMod.val_lt j⟩
  · intro a _ b _ hab
    exact ZMod.val_injective N hab
  · intro k hk
    refine ⟨((k : ℕ) : ZMod N), ?_, ?_⟩
    · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h0
      have hval : (((k : ℕ) : ZMod N)).val = 0 := by rw [h0]; exact ZMod.val_zero
      rw [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hk).2] at hval
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      omega
    · exact ZMod.val_cast_of_lt (Finset.mem_Ico.mp hk).2
  · intro j _
    rw [ZMod.natCast_zmod_val]

/-- If 2(2r + 1) ≤ N and N ≥ 2, the sum of the absolute battleship eigenvalues is at most √N +
(2/√N)N(1 + log N). -/
lemma absEigen_sum_le {r : ℕ} (h : 2 * (2 * r + 1) ≤ N) (hN2 : 2 ≤ N) :
    ∑ j : ZMod N, absEigen (bsCoeff (N := N) r) j
      ≤ Real.sqrt N + (2 / Real.sqrt N) * ((N : ℝ) * (1 + Real.log N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hd : 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h' : ((2 * (2 * r + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    push_cast at h'
    push_cast
    linarith
  have h0 : absEigen (bsCoeff (N := N) r) 0 ≤ Real.sqrt N := by
    rw [absEigen_bs_zero h]
    calc ((N : ℝ) - 2 * ((2 * r + 1 : ℕ) : ℝ)) / Real.sqrt N
        ≤ (N : ℝ) / Real.sqrt N := div_le_div_of_nonneg_right (by linarith) hsqrt.le
      _ = Real.sqrt N := Real.div_sqrt
  have hrest : ∑ j ∈ Finset.univ.erase (0 : ZMod N), absEigen (bsCoeff (N := N) r) j
      ≤ (2 / Real.sqrt N) * ((N : ℝ) * (1 + Real.log N)) := by
    rw [sum_erase_zero_eq (fun j => absEigen (bsCoeff (N := N) r) j)]
    calc ∑ k ∈ Finset.Ico 1 N, absEigen (bsCoeff (N := N) r) ((k : ℕ) : ZMod N)
        ≤ ∑ k ∈ Finset.Ico 1 N, (2 / Real.sqrt N) * bsCsc (N := N) k := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
          have hkN : k < N := (Finset.mem_Ico.mp hk).2
          have hne : ((k : ℕ) : ZMod N) ≠ 0 := by
            intro hzero
            have hval : (((k : ℕ) : ZMod N)).val = 0 := by rw [hzero]; exact ZMod.val_zero
            rw [ZMod.val_cast_of_lt hkN] at hval
            omega
          have hle := absEigen_le_csc (N := N) (r := r) (by omega) hne
          rwa [ZMod.val_cast_of_lt hkN] at hle
      _ = (2 / Real.sqrt N) * ∑ k ∈ Finset.Ico 1 N, bsCsc (N := N) k := by
          rw [Finset.mul_sum]
      _ ≤ (2 / Real.sqrt N) * ((N : ℝ) * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left (bs_csc_sum_le hN2) (by positivity)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (ZMod N))
    (fun j => absEigen (bsCoeff (N := N) r) j) (Finset.mem_univ 0)
  rw [← hsplit]
  linarith

/-- If 2(2r + 1) ≤ N and N ≥ 2, the mean absolute battleship eigenvalue is at most 3(1 + log
N)/√N, as used in [HunzikerEtAl2003]. -/
theorem bsS_le {r : ℕ} (h : 2 * (2 * r + 1) ≤ N) (hN2 : 2 ≤ N) :
    bsS (N := N) r ≤ 3 * (1 + Real.log N) / Real.sqrt N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsum := absEigen_sum_le h hN2
  unfold bsS
  calc ((N : ℝ))⁻¹ * ∑ j : ZMod N, absEigen (bsCoeff (N := N) r) j
      ≤ ((N : ℝ))⁻¹
          * (Real.sqrt N + (2 / Real.sqrt N) * ((N : ℝ) * (1 + Real.log N))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 + 2 * (1 + Real.log N)) / Real.sqrt N := by
        field_simp
        rw [Real.sq_sqrt hN.le]
        ring
    _ ≤ 3 * (1 + Real.log N) / Real.sqrt N := by
        apply div_le_div_of_nonneg_right _ hsqrt.le
        linarith

/-- For θ ≥ 0, the amplification success probability is at most ((2m + 1)θ)². -/
lemma successProb_le_sq {θ : ℝ} (hθ0 : 0 ≤ θ) (m : ℕ) :
    successProb θ m ≤ ((((2 * m + 1 : ℕ) : ℝ)) * θ) ^ 2 := by
  unfold successProb
  set x : ℝ := (((2 * m + 1 : ℕ) : ℝ)) * θ with hx_def
  have hx0 : 0 ≤ x := by positivity
  rcases le_or_gt x 1 with hx1 | hx1
  · have hxpi : x ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
    exact pow_le_pow_left₀ hs0 (Real.sin_le hx0) 2
  · have hs1 : Real.sin x ^ 2 ≤ 1 := by
      have h := Real.abs_sin_le_one x
      have hsq : |Real.sin x| ^ 2 = Real.sin x ^ 2 := sq_abs (Real.sin x)
      nlinarith [abs_nonneg (Real.sin x)]
    have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
    linarith

/-- For s = sin θ with s > 0 and 0 < θ ≤ π/2, success probability at least 1/2 requires 2m + 1 ≥
√2/(πs). This is the amplification lower-bound estimate used in [HunzikerEtAl2003]. -/
theorem bigship_iterations_lower {s θ : ℝ} (hs : 0 < s) (hθeq : Real.sin θ = s)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2) {m : ℕ}
    (hsucc : 1 / 2 ≤ successProb θ m) :
    (Real.sqrt 2 / Real.pi) / s ≤ 2 * (m : ℝ) + 1 := by
  set x : ℝ := (((2 * m + 1 : ℕ) : ℝ)) * θ with hx_def
  have hx0 : 0 ≤ x := by positivity
  have hsq : (1 : ℝ) / 2 ≤ x ^ 2 := le_trans hsucc (successProb_le_sq hθ0.le m)
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hhalf : (1 : ℝ) / Real.sqrt 2 ≤ x := by
    have h2 : ((1 : ℝ) / Real.sqrt 2) ^ 2 ≤ x ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
      linarith
    have habs := (sq_le_sq.mp h2)
    rwa [abs_of_pos (by positivity), abs_of_nonneg hx0] at habs
  have hjordan := Real.mul_le_sin hθ0.le hθ2
  rw [hθeq] at hjordan
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcoef : (2 / Real.pi) * (Real.pi / 2) = 1 := by field_simp
  have hθle : θ ≤ Real.pi / 2 * s := by nlinarith
  have hxle : x ≤ (((2 * m + 1 : ℕ) : ℝ)) * (Real.pi / 2 * s) :=
    mul_le_mul_of_nonneg_left hθle (by positivity)
  have hmain : (1 : ℝ) / Real.sqrt 2 ≤ (((2 * m + 1 : ℕ) : ℝ)) * (Real.pi / 2 * s) :=
    le_trans hhalf hxle
  have hpos : (0 : ℝ) < Real.pi / 2 * s := by positivity
  have hconv : (Real.sqrt 2 / Real.pi) / s
      = (1 / Real.sqrt 2) / (Real.pi / 2 * s) := by
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hconv]
  have := (div_le_iff₀ hpos).mpr hmain
  calc (1 / Real.sqrt 2) / (Real.pi / 2 * s) ≤ (((2 * m + 1 : ℕ) : ℝ)) := this
    _ = 2 * (m : ℝ) + 1 := by push_cast; ring

/-- If 2(2r + 1) ≤ N and N ≥ 2, amplification with success probability at least 1/2 requires 2m
+ 1 ≥ (√2/π)√N/(3(1 + log N)), as in the battleship analysis of [HunzikerEtAl2003]. -/
theorem bigship_queries_lower {r : ℕ} (h : 2 * (2 * r + 1) ≤ N) (hN2 : 2 ≤ N)
    {m : ℕ} (hsucc : 1 / 2 ≤ successProb (bsTheta (N := N) r) m) :
    (Real.sqrt 2 / Real.pi) * Real.sqrt N / (3 * (1 + Real.log N)) ≤ 2 * (m : ℝ) + 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsSle : bsS (N := N) r ≤ 3 * (1 + Real.log N) / Real.sqrt N := bsS_le h hN2
  set s := min (bsS (N := N) r) 1 with hs_def
  have hsnonneg : 0 ≤ s := le_min (bsS_nonneg (N := N) r) (by norm_num)
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hsnonneg with h | h
    · exact h
    · exfalso
      have hzero : min (bsS (N := N) r) 1 = 0 := by
        rw [← hs_def]; exact h.symm
      have hθzero : bsTheta (N := N) r = 0 := by
        unfold bsTheta
        rw [hzero, Real.arcsin_zero]
      have hprob : successProb (bsTheta (N := N) r) m = 0 := by
        rw [hθzero]
        unfold successProb
        simp
      rw [hprob] at hsucc
      norm_num at hsucc
  have hsle : s ≤ 1 := min_le_right _ _
  have hsleS : s ≤ bsS (N := N) r := min_le_left _ _
  have hsin : Real.sin (bsTheta (N := N) r) = s :=
    Real.sin_arcsin (by linarith [le_of_lt hspos]) hsle
  have hθ0 : 0 < bsTheta (N := N) r := Real.arcsin_pos.mpr hspos
  have hθ2 : bsTheta (N := N) r ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hiter := bigship_iterations_lower hspos hsin hθ0 hθ2 hsucc
  have hsle' : s ≤ 3 * (1 + Real.log N) / Real.sqrt N := le_trans hsleS hsSle
  have hpos3 : (0 : ℝ) < 3 * (1 + Real.log N) / Real.sqrt N := by
    have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  have hinv : Real.sqrt N / (3 * (1 + Real.log N)) ≤ s⁻¹ := by
    have h2 : (3 * (1 + Real.log N) / Real.sqrt N)⁻¹ ≤ s⁻¹ :=
      (inv_le_inv₀ hpos3 hspos).mpr hsle'
    have heq : Real.sqrt N / (3 * (1 + Real.log N))
        = (3 * (1 + Real.log N) / Real.sqrt N)⁻¹ := by
      rw [inv_div]
    rwa [heq]
  have hconst : (0 : ℝ) < Real.sqrt 2 / Real.pi := by positivity
  have hiter' : (Real.sqrt 2 / Real.pi) * s⁻¹ ≤ 2 * (m : ℝ) + 1 := by
    simpa [div_eq_mul_inv] using hiter
  calc (Real.sqrt 2 / Real.pi) * Real.sqrt N / (3 * (1 + Real.log N))
      = (Real.sqrt 2 / Real.pi) * (Real.sqrt N / (3 * (1 + Real.log N))) := by ring
    _ ≤ (Real.sqrt 2 / Real.pi) * s⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hconst.le
    _ ≤ 2 * (m : ℝ) + 1 := hiter'

/-- The battleship value oracle, equal to 1 when `a - x` lies in the ship window and 0
otherwise. -/
noncomputable def bsValue (r : ℕ) (a x : ZMod N) : ℂ :=
  if a - x ∈ shipWindow (N := N) r then 1 else 0

omit [NeZero N] in

/-- A residue lies in the ship window exactly when it equals t - r for some natural number t ≤
2r. -/
lemma mem_shipWindow_iff {r : ℕ} (k : ZMod N) :
    k ∈ shipWindow (N := N) r
      ↔ ∃ t : ℕ, t ≤ 2 * r ∧ k = ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) := by
  unfold shipWindow
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Nat.lt_succ_iff.mp (Finset.mem_range.mp ht), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht), rfl⟩

omit [NeZero N] in

/-- If 2r + 1 ≤ N, equal shifted residues with natural parameters at most 2r have equal
parameters. -/
lemma shipWindow_shift_inj {r : ℕ} (h : 2 * r + 1 ≤ N) {t t' : ℕ}
    (ht : t ≤ 2 * r) (ht' : t' ≤ 2 * r)
    (heq : ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N)
      = ((t' : ℕ) : ZMod N) - ((r : ℕ) : ZMod N)) : t = t' := by
  have hcast : ((t : ℕ) : ZMod N) = ((t' : ℕ) : ZMod N) := by
    have := congrArg (fun z => z + ((r : ℕ) : ZMod N)) heq
    simpa [sub_add_cancel] using this
  have hmod := (ZMod.natCast_eq_natCast_iff t t' N).mp hcast
  exact Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)

/-- The left endpoint -r belongs to the cyclic ship window. -/
lemma neg_r_mem_window (r : ℕ) :
    -((r : ℕ) : ZMod N) ∈ shipWindow (N := N) r := by
  rw [mem_shipWindow_iff]
  exact ⟨0, by omega, by simp⟩

/-- If 2r + 1 < N, the residue -(r + 1) does not belong to the ship window. -/
lemma neg_succ_r_not_mem_window {r : ℕ} (h : 2 * r + 1 < N) :
    -(((r + 1 : ℕ)) : ZMod N) ∉ shipWindow (N := N) r := by
  rw [mem_shipWindow_iff]
  rintro ⟨t, ht, heq⟩
  have hcast : ((t + 1 : ℕ) : ZMod N) = 0 := by
    have hcongr := congrArg (fun z => z + (((r + 1 : ℕ)) : ZMod N)) heq
    push_cast at hcongr
    calc ((t + 1 : ℕ) : ZMod N) = ((t : ℕ) : ZMod N) + 1 := by push_cast; ring
      _ = 0 := by
        rw [eq_comm]
        calc (0 : ZMod N) = ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) + (((r : ℕ) : ZMod N) + 1) := by simpa using hcongr
          _ = ((t : ℕ) : ZMod N) + 1 := by ring
  have hlt : t + 1 < N := by omega
  have hpos : 0 < t + 1 := by omega
  have hdvd : N ∣ t + 1 := (ZMod.natCast_eq_zero_iff (t + 1) N).mp hcast
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- If 2r + 1 < N, two battleship value oracles agree everywhere exactly when the second oracle
takes values 1 and 0 at the two stated boundary queries. This is the oracle-equivalence
criterion used in [HunzikerEtAl2003]. -/
theorem equiv_oracle_iff {r : ℕ} (h : 2 * r + 1 < N) (a a' : ZMod N) :
    (∀ x, bsValue (N := N) r a' x = bsValue (N := N) r a x)
      ↔ bsValue (N := N) r a' (a + ((r : ℕ) : ZMod N)) = 1
        ∧ bsValue (N := N) r a' (a + (((r + 1 : ℕ)) : ZMod N)) = 0 := by
  have hle : 2 * r + 1 ≤ N := le_of_lt h
  have hvalr : a - (a + ((r : ℕ) : ZMod N)) = -((r : ℕ) : ZMod N) := by abel
  have hvals : a - (a + (((r + 1 : ℕ)) : ZMod N)) = -(((r + 1 : ℕ)) : ZMod N) := by abel
  constructor
  · intro heq
    constructor
    · rw [heq, bsValue, ite_eq_left (hvalr ▸ neg_r_mem_window (N := N) r)]
    · rw [heq, bsValue, ite_eq_right (hvals ▸ neg_succ_r_not_mem_window h)]
  · rintro ⟨h1, h2⟩

    have hd1 : a' - (a + ((r : ℕ) : ZMod N)) ∈ shipWindow (N := N) r := by
      by_contra hc
      have : bsValue (N := N) r a' (a + ((r : ℕ) : ZMod N)) = 0 := by
        unfold bsValue; rw [ite_eq_right hc]
      rw [this] at h1
      norm_num at h1
    obtain ⟨t, ht, ht_eq⟩ := (mem_shipWindow_iff (N := N) (r := r) _).mp hd1
    have hd : a' - a = ((t : ℕ) : ZMod N) := by
      have : a' - (a + ((r : ℕ) : ZMod N)) = ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) := ht_eq
      have h2' : a' - a - ((r : ℕ) : ZMod N) = ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) := by
        rw [← this]; abel
      have := congrArg (fun z => z + ((r : ℕ) : ZMod N)) h2'
      simpa [sub_add_cancel] using this
    have hd2_not : a' - (a + (((r + 1 : ℕ)) : ZMod N)) ∉ shipWindow (N := N) r := by
      by_contra hc
      have : bsValue (N := N) r a' (a + (((r + 1 : ℕ)) : ZMod N)) = 1 := by
        unfold bsValue; rw [ite_eq_left hc]
      rw [this] at h2
      norm_num at h2
    have ht0 : t = 0 := by
      by_contra htne
      have htpos : 1 ≤ t := Nat.pos_of_ne_zero htne
      apply hd2_not
      rw [mem_shipWindow_iff]
      refine ⟨t - 1, by omega, ?_⟩
      have hcast : ((t - 1 : ℕ) : ZMod N) = ((t : ℕ) : ZMod N) - 1 := by
        rw [Nat.cast_sub htpos]; push_cast; ring
      have hexpr : a' - (a + (((r + 1 : ℕ)) : ZMod N))
          = ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) - 1 := by
        rw [show a' - (a + (((r + 1 : ℕ)) : ZMod N)) = a' - a - (((r + 1 : ℕ)) : ZMod N) by abel]
        rw [hd]
        push_cast
        abel
      rw [hexpr, hcast]
      abel
    have haa : a' = a := by
      rw [← sub_eq_zero] at hd ⊢
      rw [← hd, ht0]; simp
    subst haa
    intro x
    rfl

end Qatlib.Papers.QLearningGeom03.MainResults
