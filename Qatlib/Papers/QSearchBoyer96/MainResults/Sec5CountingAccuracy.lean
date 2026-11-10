/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchBoyer96.MainResults

open Real

def periodCount (P theta : ℝ) : ℝ := P * theta / Real.pi

def angleFromPeriod (P fEst : ℝ) : ℝ := fEst * Real.pi / P

def countEstimate (N theta : ℝ) : ℝ := N * Real.sin theta ^ 2

theorem amplitude_period (theta : ℝ) (f : ℤ) (P j : ℕ)
    (hPtheta : (P : ℝ) * theta = Real.pi * (f : ℝ)) :
    Real.sin ((2 * ((j + P : ℕ) : ℝ) + 1) * theta) =
      Real.sin ((2 * (j : ℝ) + 1) * theta) := by
  have harg : (2 * ((j + P : ℕ) : ℝ) + 1) * theta =
      (2 * (j : ℝ) + 1) * theta + (f : ℝ) * (2 * Real.pi) := by
    push_cast
    nlinarith [hPtheta]
  rw [harg]
  exact Real.sin_add_int_mul_two_pi _ _

theorem angle_error_of_period_error (P theta fEst : ℝ) (hP : 0 < P)
    (hf : |periodCount P theta - fEst| < 1) :
    |theta - angleFromPeriod P fEst| < Real.pi / P := by
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkey : theta - angleFromPeriod P fEst =
      (periodCount P theta - fEst) * (Real.pi / P) := by
    unfold angleFromPeriod periodCount
    field_simp
  have hpos : (0 : ℝ) < Real.pi / P := by positivity
  rw [hkey, abs_mul, abs_of_pos hpos]
  nlinarith [hf]

theorem count_error_bound (N P theta thetaEst : ℝ) (hN : 0 < N) (hP : 0 < P)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hthetaEst0 : 0 ≤ thetaEst) (hthetaEstpi : thetaEst ≤ Real.pi)
    (hclose : |theta - thetaEst| < Real.pi / P) :
    |countEstimate N theta - countEstimate N thetaEst| <
      (2 * Real.pi / P) * Real.sqrt (countEstimate N theta * N) +
        (Real.pi / P) ^ 2 * N := by
  have hpiP : (0 : ℝ) < Real.pi / P := by positivity
  have hsin0 : 0 ≤ Real.sin theta := Real.sin_nonneg_of_nonneg_of_le_pi htheta0 hthetapi
  have hsinEst0 : 0 ≤ Real.sin thetaEst :=
    Real.sin_nonneg_of_nonneg_of_le_pi hthetaEst0 hthetaEstpi
  have hdelta : |Real.sin theta - Real.sin thetaEst| < Real.pi / P :=
    lt_of_le_of_lt (Real.abs_sin_sub_sin_le theta thetaEst) hclose
  have hdelta0 : 0 ≤ |Real.sin theta - Real.sin thetaEst| := abs_nonneg _

  have hfactor : Real.sin theta ^ 2 - Real.sin thetaEst ^ 2 =
      (Real.sin theta - Real.sin thetaEst) * (Real.sin theta + Real.sin thetaEst) := by
    ring
  have hsum : |Real.sin theta + Real.sin thetaEst| ≤
      2 * Real.sin theta + |Real.sin theta - Real.sin thetaEst| := by
    have hup : Real.sin theta + Real.sin thetaEst ≤
        2 * Real.sin theta + |Real.sin theta - Real.sin thetaEst| := by
      have h1 : Real.sin thetaEst - Real.sin theta ≤
          |Real.sin thetaEst - Real.sin theta| := le_abs_self _
      rw [abs_sub_comm] at h1
      linarith
    have hlow : -(2 * Real.sin theta + |Real.sin theta - Real.sin thetaEst|) ≤
        Real.sin theta + Real.sin thetaEst := by
      linarith [hsin0, hsinEst0, hdelta0]
    exact abs_le.2 ⟨hlow, hup⟩
  have hsq : |Real.sin theta ^ 2 - Real.sin thetaEst ^ 2| <
      2 * Real.sin theta * (Real.pi / P) + (Real.pi / P) ^ 2 := by
    have hprod : |Real.sin theta ^ 2 - Real.sin thetaEst ^ 2| =
        |Real.sin theta - Real.sin thetaEst| *
          |Real.sin theta + Real.sin thetaEst| := by
      rw [hfactor, abs_mul]
    have hdist : |Real.sin theta - Real.sin thetaEst| *
          |Real.sin theta + Real.sin thetaEst| ≤
        |Real.sin theta - Real.sin thetaEst| *
          (2 * Real.sin theta + |Real.sin theta - Real.sin thetaEst|) :=
      mul_le_mul_of_nonneg_left hsum hdelta0
    have hexpand : |Real.sin theta - Real.sin thetaEst| *
          (2 * Real.sin theta + |Real.sin theta - Real.sin thetaEst|) =
        2 * Real.sin theta * |Real.sin theta - Real.sin thetaEst| +
          |Real.sin theta - Real.sin thetaEst| ^ 2 := by
      ring
    have hA : 2 * Real.sin theta * |Real.sin theta - Real.sin thetaEst| ≤
        2 * Real.sin theta * (Real.pi / P) :=
      mul_le_mul_of_nonneg_left (le_of_lt hdelta)
        (by linarith : (0 : ℝ) ≤ 2 * Real.sin theta)
    have hB : |Real.sin theta - Real.sin thetaEst| ^ 2 < (Real.pi / P) ^ 2 := by
      nlinarith [hdelta, hdelta0, hpiP]
    nlinarith [hprod, hdist, hexpand, hA, hB]
  have hsqrt : Real.sqrt (countEstimate N theta * N) = N * Real.sin theta := by
    unfold countEstimate
    rw [show N * Real.sin theta ^ 2 * N = (N * Real.sin theta) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (le_of_lt hN) hsin0)
  have hcount : countEstimate N theta - countEstimate N thetaEst =
      N * (Real.sin theta ^ 2 - Real.sin thetaEst ^ 2) := by
    unfold countEstimate
    ring
  rw [hcount, abs_mul, abs_of_pos hN, hsqrt]
  have hmul := mul_lt_mul_of_pos_left hsq hN
  have hrhs : N * (2 * Real.sin theta * (Real.pi / P) + (Real.pi / P) ^ 2) =
      (2 * Real.pi / P) * (N * Real.sin theta) + (Real.pi / P) ^ 2 * N := by
    ring
  rw [hrhs] at hmul
  exact hmul

theorem counting_error_from_period_readout (N P theta fEst : ℝ) (hN : 0 < N) (hP : 0 < P)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hreadout : |periodCount P theta - fEst| < 1)
    (hthetaEst0 : 0 ≤ angleFromPeriod P fEst)
    (hthetaEstpi : angleFromPeriod P fEst ≤ Real.pi) :
    |countEstimate N theta - countEstimate N (angleFromPeriod P fEst)| <
      (2 * Real.pi / P) * Real.sqrt (countEstimate N theta * N) +
        (Real.pi / P) ^ 2 * N :=
  count_error_bound N P theta (angleFromPeriod P fEst) hN hP htheta0 hthetapi
    hthetaEst0 hthetaEstpi (angle_error_of_period_error P theta fEst hP hreadout)

theorem count_error_bound_scaled (N c theta thetaEst : ℝ) (hN : 0 < N) (hc : 0 < c)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hthetaEst0 : 0 ≤ thetaEst) (hthetaEstpi : thetaEst ≤ Real.pi)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt N)) :
    |countEstimate N theta - countEstimate N thetaEst| <
      (2 * Real.pi / c) * Real.sqrt (countEstimate N theta) + (Real.pi / c) ^ 2 := by
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hcN : 0 < c * Real.sqrt N := by positivity
  have hmain := count_error_bound N (c * Real.sqrt N) theta thetaEst hN hcN
    htheta0 hthetapi hthetaEst0 hthetaEstpi hclose
  have ht0 : 0 ≤ countEstimate N theta := by
    unfold countEstimate
    positivity
  have hterm1 : (2 * Real.pi / (c * Real.sqrt N)) *
      Real.sqrt (countEstimate N theta * N) =
      (2 * Real.pi / c) * Real.sqrt (countEstimate N theta) := by
    rw [Real.sqrt_mul ht0]
    have hsN : Real.sqrt N ≠ 0 := ne_of_gt hsqrtN
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
  have hterm2 : (Real.pi / (c * Real.sqrt N)) ^ 2 * N = (Real.pi / c) ^ 2 := by
    have hsq : (c * Real.sqrt N) ^ 2 = c ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hN)]
    rw [div_pow, hsq]
    have hc0 : c ^ 2 * N ≠ 0 := by positivity
    field_simp
  rw [hterm1, hterm2] at hmain
  exact hmain

theorem count_error_bound_relative (N t c theta thetaEst : ℝ) (hN : 0 < N) (ht : 0 < t)
    (hc : 0 < c)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hthetaEst0 : 0 ≤ thetaEst) (hthetaEstpi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (N / t))) :
    |countEstimate N theta - countEstimate N thetaEst| <
      t * ((1 + Real.pi / c) ^ 2 - 1) := by
  have hNt : 0 < N / t := by positivity
  have hsqrtNt : 0 < Real.sqrt (N / t) := Real.sqrt_pos.2 hNt
  have hcNt : 0 < c * Real.sqrt (N / t) := by positivity
  have hmain := count_error_bound N (c * Real.sqrt (N / t)) theta thetaEst hN hcNt
    htheta0 hthetapi hthetaEst0 hthetaEstpi hclose
  have hsq : (c * Real.sqrt (N / t)) ^ 2 = c ^ 2 * (N / t) := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hNt)]
  have hterm1 : (2 * Real.pi / (c * Real.sqrt (N / t))) *
      Real.sqrt (countEstimate N theta * N) = (2 * Real.pi / c) * t := by
    rw [hcount, Real.sqrt_mul (le_of_lt ht), Real.sqrt_div (le_of_lt hN) t]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
    rw [Real.sq_sqrt (le_of_lt ht)]
  have hterm2 : (Real.pi / (c * Real.sqrt (N / t))) ^ 2 * N = (Real.pi / c) ^ 2 * t := by
    rw [div_pow, hsq]
    have hc0 : c ^ 2 * (N / t) ≠ 0 := by positivity
    field_simp
  rw [hterm1, hterm2] at hmain
  rw [hcount] at hmain ⊢
  have hexpand : (1 + Real.pi / c) ^ 2 - 1 = 2 * Real.pi / c + (Real.pi / c) ^ 2 := by
    ring
  rw [hexpand]
  linarith [hmain]

theorem count_error_bound_second_pass (N t c theta thetaEst : ℝ) (hN : 0 < N) (ht : 0 < t)
    (hc : 0 < c)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hthetaEst0 : 0 ≤ thetaEst) (hthetaEstpi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (t * N))) :
    |countEstimate N theta - countEstimate N thetaEst| <
      2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) := by
  have htN : 0 < t * N := by positivity
  have hcNt : 0 < c * Real.sqrt (t * N) := by positivity
  have hmain := count_error_bound N (c * Real.sqrt (t * N)) theta thetaEst hN hcNt
    htheta0 hthetapi hthetaEst0 hthetaEstpi hclose
  have hterm1 : (2 * Real.pi / (c * Real.sqrt (t * N))) *
      Real.sqrt (countEstimate N theta * N) = 2 * Real.pi / c := by
    rw [hcount, Real.sqrt_mul (le_of_lt ht)]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
  have hterm2 : (Real.pi / (c * Real.sqrt (t * N))) ^ 2 * N =
      Real.pi ^ 2 / (c ^ 2 * t) := by
    have hsq : (c * Real.sqrt (t * N)) ^ 2 = c ^ 2 * (t * N) := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt htN)]
    rw [div_pow, hsq]
    have hc0 : c ^ 2 * (t * N) ≠ 0 := by positivity
    field_simp
  rw [hterm1, hterm2] at hmain
  exact hmain

theorem second_pass_error_lt_half {c t : ℝ} (hc : 14 ≤ c) (ht : 1 ≤ t) :
    2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) < 1 / 2 := by
  have hcpos : (0 : ℝ) < c := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_sq : Real.pi ^ 2 < 3.1416 ^ 2 := by
    nlinarith [Real.pi_lt_d4, hpi_pos]
  have h1 : 2 * Real.pi / c ≤ 2 * Real.pi / 14 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hc
  have h2 : Real.pi ^ 2 / (c ^ 2 * t) ≤ Real.pi ^ 2 / (14 ^ 2 * 1) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · norm_num
    · nlinarith [ht, hc]
  nlinarith [h1, h2, hpi_sq]

theorem count_error_lt_half (N t c theta thetaEst : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (hc : 14 ≤ c)
    (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi)
    (hthetaEst0 : 0 ≤ thetaEst) (hthetaEstpi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (t * N))) :
    |countEstimate N theta - countEstimate N thetaEst| < 1 / 2 :=
  lt_of_lt_of_le
    (count_error_bound_second_pass N t c theta thetaEst hN (by linarith) (by linarith)
      htheta0 hthetapi hthetaEst0 hthetaEstpi hcount hclose)
    (le_of_lt (second_pass_error_lt_half hc ht))

theorem count_round_eq_of_error_lt_half {t tEst : ℝ} {n : ℕ} (hn : t = n)
    (hclose : |tEst - t| < 1 / 2) : ⌊tEst + 1 / 2⌋ = (n : ℤ) := by
  have h1 : (n : ℝ) ≤ tEst + 1 / 2 := by
    have := abs_lt.1 hclose
    rw [hn] at this
    linarith [this.1]
  have h2 : tEst + 1 / 2 < (n : ℝ) + 1 := by
    have := abs_lt.1 hclose
    rw [hn] at this
    linarith [this.2]
  simpa using (Int.floor_eq_iff.2 ⟨h1, h2⟩ : ⌊tEst + 1 / 2⌋ = (n : ℤ))

end Qatlib.Papers.QSearchBoyer96.MainResults
