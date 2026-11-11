/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantum counting accuracy

The definitions `periodCount`, `angleFromPeriod`, and `countEstimate` relate Fourier period
estimates to marked item counts. The estimates formalize the error bounds and precision
tradeoffs from Section 5 of [BoyerEtAl1998], including exact recovery by rounding once the error
is below one half.

## Main statements

* `count_error_bound`: Bounds the count error using angular accuracy π/P.
* `count_error_lt_half`: Gives sufficient second pass precision for error below one half.
* `count_round_eq_of_error_lt_half`: Recovers an integer count by rounding.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchBoyer98.MainResults

open Real

/-- The Fourier period parameter Pθ/π associated with angle θ. -/
def periodCount (P theta : ℝ) : ℝ := P * theta / Real.pi

/-- The angle estimate obtained by multiplying a period estimate by π/P. -/
def angleFromPeriod (P fEst : ℝ) : ℝ := fEst * Real.pi / P

/-- The marked count estimate N sin² θ determined by an angle θ. -/
def countEstimate (N theta : ℝ) : ℝ := N * Real.sin theta ^ 2

/-- For positive P, period error strictly below one gives angular error strictly below π/P. -/
theorem angle_error_of_period_error (P theta fEst : ℝ) (hP : 0 < P)
    (hf : |periodCount P theta - fEst| < 1) :
    |theta - angleFromPeriod P fEst| < Real.pi / P := by
  have hkey : theta - angleFromPeriod P fEst =
      (periodCount P theta - fEst) * (Real.pi / P) := by
    unfold angleFromPeriod periodCount
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.pi / P)]
  have : (0:ℝ) < Real.pi / P := by positivity
  nlinarith [hf]

/-- For angles in [0, π] at distance less than π/P, bounds the count error by (2π/P)√(tN) +
(π/P)²N, where t is the original count estimate. See [BoyerEtAl1998]. -/
theorem count_error_bound (N P theta thetaEst : ℝ) (hN : 0 < N) (hP : 0 < P)
    (htheta : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (hthetaEst : 0 ≤ thetaEst) (hthetaEst_pi : thetaEst ≤ Real.pi)
    (hclose : |theta - thetaEst| < Real.pi / P) :
    |countEstimate N theta - countEstimate N thetaEst| <
      (2 * Real.pi / P) * Real.sqrt (countEstimate N theta * N) +
        (Real.pi / P) ^ 2 * N := by
  set s := Real.sin theta with hs
  set s' := Real.sin thetaEst with hs'
  have hsnonneg : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi htheta htheta_pi
  have hs'nonneg : 0 ≤ s' := Real.sin_nonneg_of_nonneg_of_le_pi hthetaEst hthetaEst_pi
  have hd : |s - s'| < Real.pi / P :=
    lt_of_le_of_lt (Real.abs_sin_sub_sin_le theta thetaEst) hclose
  have hdnonneg : 0 ≤ |s - s'| := abs_nonneg _
  have hpiP : (0:ℝ) < Real.pi / P := by positivity

  have hcore : |s ^ 2 - s' ^ 2| ≤ 2 * s * |s - s'| + |s - s'| ^ 2 := by
    have hsplit : s ^ 2 - s' ^ 2 = 2 * s * (s - s') - (s - s') ^ 2 := by ring
    have hdsq : (s - s') ^ 2 = |s - s'| ^ 2 := (sq_abs (s - s')).symm
    have h1 : 2 * s * (s - s') ≤ 2 * s * |s - s'| := by
      have := mul_le_mul_of_nonneg_left (le_abs_self (s - s')) (by linarith : (0:ℝ) ≤ 2 * s)
      linarith
    have h3 : s ^ 2 - s' ^ 2 ≤ 2 * s * |s - s'| + |s - s'| ^ 2 := by
      rw [hsplit]; linarith [h1, hdsq, sq_nonneg |s - s'|]
    have h4 : -(2 * s * |s - s'| + |s - s'| ^ 2) ≤ s ^ 2 - s' ^ 2 := by
      have hneg : -|s - s'| ≤ s - s' := neg_abs_le (s - s')
      have h4a : -2 * s * |s - s'| ≤ 2 * s * (s - s') := by nlinarith
      have h4b : -|s - s'| ^ 2 ≤ -(s - s') ^ 2 := by linarith [hdsq]
      rw [hsplit]; linarith
    exact abs_le.2 ⟨h4, h3⟩

  have hstrict : |s ^ 2 - s' ^ 2| < 2 * s * (Real.pi / P) + (Real.pi / P) ^ 2 := by
    have hsq : |s - s'| ^ 2 < (Real.pi / P) ^ 2 := by
      nlinarith [hd, hdnonneg, hpiP]
    have hmul : 2 * s * |s - s'| ≤ 2 * s * (Real.pi / P) := by
      have := mul_le_mul_of_nonneg_left (le_of_lt hd) (by linarith : (0:ℝ) ≤ 2 * s)
      linarith
    nlinarith [hcore, hsq, hmul]
  have hcount : countEstimate N theta - countEstimate N thetaEst =
      N * (s ^ 2 - s' ^ 2) := by
    unfold countEstimate
    rw [← hs, ← hs']
    ring
  have hsqrt : Real.sqrt (countEstimate N theta * N) = N * s := by
    unfold countEstimate
    rw [← hs]
    rw [show N * s ^ 2 * N = (N * s) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (le_of_lt hN) hsnonneg)
  rw [hcount, abs_mul, abs_of_pos hN, hsqrt]
  have hmul := mul_lt_mul_of_pos_left hstrict hN
  have hrhs : N * (2 * s * (Real.pi / P) + (Real.pi / P) ^ 2) =
      (2 * Real.pi / P) * (N * s) + (Real.pi / P) ^ 2 * N := by ring
  rw [hrhs] at hmul
  exact hmul

/-- At angular precision π/(c√N), bounds the count error by (2π/c)√t + (π/c)² for positive N and
c. -/
theorem count_error_bound_scaled (N c theta thetaEst : ℝ) (hN : 0 < N) (hc : 0 < c)
    (htheta : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (hthetaEst : 0 ≤ thetaEst) (hthetaEst_pi : thetaEst ≤ Real.pi)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt N)) :
    |countEstimate N theta - countEstimate N thetaEst| <
      (2 * Real.pi / c) * Real.sqrt (countEstimate N theta) + (Real.pi / c) ^ 2 := by
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hcN : 0 < c * Real.sqrt N := by positivity
  have hmain := count_error_bound N (c * Real.sqrt N) theta thetaEst hN hcN
    htheta htheta_pi hthetaEst hthetaEst_pi hclose
  have hsq : (c * Real.sqrt N) ^ 2 = c ^ 2 * N := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hN)]

  have hterm1 : (2 * Real.pi / (c * Real.sqrt N)) *
      Real.sqrt (countEstimate N theta * N) =
      (2 * Real.pi / c) * Real.sqrt (countEstimate N theta) := by
    have ht0 : 0 ≤ countEstimate N theta := by
      unfold countEstimate
      positivity
    rw [show Real.sqrt (countEstimate N theta * N) =
        Real.sqrt (countEstimate N theta) * Real.sqrt N by
      rw [Real.sqrt_mul ht0]]
    field_simp
  have hterm2 : (Real.pi / (c * Real.sqrt N)) ^ 2 * N = (Real.pi / c) ^ 2 := by
    rw [div_pow, hsq]
    field_simp
  rw [hterm1, hterm2] at hmain
  exact hmain

/-- At angular precision π/(c√(N/t)), bounds the absolute count error by t((1 + π/c)² − 1),
assuming the original estimate equals positive t. -/
theorem count_error_bound_relative (N t c theta thetaEst : ℝ) (hN : 0 < N)
    (ht : 0 < t) (hc : 0 < c)
    (htheta : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (hthetaEst : 0 ≤ thetaEst) (hthetaEst_pi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (N / t))) :
    |countEstimate N theta - countEstimate N thetaEst| <
      t * ((1 + Real.pi / c) ^ 2 - 1) := by
  have hNt : 0 < N / t := by positivity
  have hsqrtNt : 0 < Real.sqrt (N / t) := Real.sqrt_pos.2 hNt
  have hcNt : 0 < c * Real.sqrt (N / t) := by positivity
  have hmain := count_error_bound N (c * Real.sqrt (N / t)) theta thetaEst hN hcNt
    htheta htheta_pi hthetaEst hthetaEst_pi hclose
  have hsqrt_tN : 0 < Real.sqrt (t * N) := Real.sqrt_pos.2 (by positivity)
  have hsq : (c * Real.sqrt (N / t)) ^ 2 = c ^ 2 * (N / t) := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hNt)]
  have hterm1 : (2 * Real.pi / (c * Real.sqrt (N / t))) *
      Real.sqrt (countEstimate N theta * N) = (2 * Real.pi / c) * t := by
    rw [hcount]
    have hsqroot : Real.sqrt (N / t) = Real.sqrt N / Real.sqrt t := by
      rw [Real.sqrt_div (le_of_lt hN)]
    rw [hsqroot, show Real.sqrt (t * N) = Real.sqrt t * Real.sqrt N by
      rw [Real.sqrt_mul (le_of_lt ht)]]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    field_simp
    exact Real.sq_sqrt (le_of_lt ht)
  have hterm2 : (Real.pi / (c * Real.sqrt (N / t))) ^ 2 * N =
      (Real.pi / c) ^ 2 * t := by
    rw [div_pow, hsq]
    field_simp
  rw [hterm1, hterm2] at hmain
  rw [hcount] at hmain ⊢
  have hsqexpand : (1 + Real.pi / c) ^ 2 - 1 = 2 * Real.pi / c + (Real.pi / c) ^ 2 := by
    ring
  rw [hsqexpand]
  nlinarith [hmain]

/-- At angular precision π/(c√(tN)), bounds the count error by 2π/c + π²/(c²t), assuming the
original estimate equals positive t. -/
theorem count_error_bound_second_pass (N t c theta thetaEst : ℝ) (hN : 0 < N)
    (ht : 0 < t) (hc : 0 < c)
    (htheta : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (hthetaEst : 0 ≤ thetaEst) (hthetaEst_pi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (t * N))) :
    |countEstimate N theta - countEstimate N thetaEst| <
      2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) := by
  have htN : 0 < t * N := by positivity
  have hsqrt : 0 < Real.sqrt (t * N) := Real.sqrt_pos.2 htN
  have hcNt : 0 < c * Real.sqrt (t * N) := by positivity
  have hmain := count_error_bound N (c * Real.sqrt (t * N)) theta thetaEst hN hcNt
    htheta htheta_pi hthetaEst hthetaEst_pi hclose
  have hsqrt_tN : Real.sqrt (t * N) ≠ 0 := ne_of_gt hsqrt
  have hterm1 : (2 * Real.pi / (c * Real.sqrt (t * N))) *
      Real.sqrt (countEstimate N theta * N) = 2 * Real.pi / c := by
    rw [hcount]
    rw [show Real.sqrt (t * N) = Real.sqrt t * Real.sqrt N by
      rw [Real.sqrt_mul (le_of_lt ht)]]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have : Real.sqrt t * Real.sqrt N ≠ 0 := by positivity
    field_simp
  have hterm2 : (Real.pi / (c * Real.sqrt (t * N))) ^ 2 * N =
      Real.pi ^ 2 / (c ^ 2 * t) := by
    rw [div_pow, show (c * Real.sqrt (t * N)) ^ 2 = c ^ 2 * (t * N) by
      rw [mul_pow, Real.sq_sqrt (le_of_lt htN)]]
    field_simp
  rw [hterm1, hterm2] at hmain
  exact hmain

/-- For c ≥ 14 and t ≥ 1, the second pass error bound 2π/c + π²/(c²t) is strictly below one
half. -/
theorem second_pass_error_lt_half {c t : ℝ} (hc : 14 ≤ c) (ht : 1 ≤ t) :
    2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) < 1 / 2 := by
  have hcpos : (0:ℝ) < c := by linarith
  have htpos : (0:ℝ) < t := by linarith
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi_pos : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi_sq : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
  have h1 : 2 * Real.pi / c ≤ 2 * Real.pi / 14 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hc
  have hden : (0:ℝ) < c ^ 2 * t := by positivity
  have h2 : Real.pi ^ 2 / (c ^ 2 * t) ≤ Real.pi ^ 2 / (14 ^ 2 * 1) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · norm_num
    · nlinarith [ht, hc]
  nlinarith [h1, h2, hpi_sq]

/-- For t ≥ 1 and c ≥ 14, angular error below π/(c√(tN)) makes the count error strictly below
one half. See [BoyerEtAl1998]. -/
theorem count_error_lt_half (N t c theta thetaEst : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (hc : 14 ≤ c)
    (htheta : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (hthetaEst : 0 ≤ thetaEst) (hthetaEst_pi : thetaEst ≤ Real.pi)
    (hcount : countEstimate N theta = t)
    (hclose : |theta - thetaEst| < Real.pi / (c * Real.sqrt (t * N))) :
    |countEstimate N theta - countEstimate N thetaEst| < 1 / 2 :=
  lt_of_lt_of_le
    (count_error_bound_second_pass N t c theta thetaEst hN (by linarith) (by linarith)
      htheta htheta_pi hthetaEst hthetaEst_pi hcount hclose)
    (le_of_lt (second_pass_error_lt_half hc ht))

/-- Rounding an estimate within strictly one half of a natural number recovers that number as an
integer. See [BoyerEtAl1998]. -/
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
  have := Int.floor_eq_iff.2 ⟨h1, h2⟩
  simpa using this

end Qatlib.Papers.QSearchBoyer98.MainResults
