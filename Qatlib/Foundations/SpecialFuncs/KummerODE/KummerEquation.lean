/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.SpecialFuncs.KummerODE.Confluent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Kummer's differential equation

This module defines `confHyper` by its confluent hypergeometric power series, together with the
reindexed derivative series `confHyperDeriv` and `confHyperSecond`. Under nonvanishing
conditions on all shifted parameters, it justifies differentiation and proves Kummer's
differential equation. Such analytic solutions form infrastructure for evolution equations, with
quantum annealing as a motivating application area [KadowakiNishimori1998].

## Main statements

* `hasDerivAt_confHyper`: identify the first derivative of the series sum.
* `hasDerivAt_confHyperDeriv`: identify its second derivative.
* `kummer_equation`: prove `zF'' + (b - z)F' - aF = 0`.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Foundations.SpecialFuncs.KummerODE

open Complex Filter
open scoped Topology

/-- The confluent hypergeometric function defined as the infinite sum of `confCoeff a b n * z ^
n`. -/
def confHyper (a b z : ℂ) : ℂ := ∑' n : ℕ, confCoeff a b n * z ^ n

/-- The power series obtained by formally differentiating the confluent hypergeometric series
once and reindexing. -/
def confHyperDeriv (a b z : ℂ) : ℂ :=
  ∑' n : ℕ, confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n

/-- The power series obtained by formally differentiating the confluent hypergeometric series
twice and reindexing. -/
def confHyperSecond (a b z : ℂ) : ℂ :=
  ∑' n : ℕ, confCoeff a b (n + 2) * ((n : ℂ) + 2) * ((n : ℂ) + 1) * z ^ n

/-- The confluent hypergeometric series has value one at zero. -/
theorem confHyper_zero (a b : ℂ) : confHyper a b 0 = 1 := by
  unfold confHyper
  rw [tsum_eq_single 0]
  · simp [confCoeff_zero]
  · intro n hn
    rw [zero_pow hn, mul_zero]

/-- Under the shifted-parameter nonvanishing hypotheses and `S ≥ 1`, the norms of the reindexed
first-derivative terms weighted by `S ^ n` are summable. -/
theorem summable_norm_confCoeff_succ_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (S : ℝ) (hS : 1 ≤ S) :
    Summable (fun n : ℕ => ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * S ^ n) := by
  have hSpos : 0 < S := by linarith
  have hbase := summable_norm_confCoeff_mul_nat_mul_pow a b ha hb S hSpos
  have htail : Summable (fun n : ℕ => ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * S ^ (n + 1)) := by
    have hshift := (summable_nat_add_iff 1).2 hbase
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) htail
  have hSpow : S ^ n ≤ S ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [pow_pos hSpos n]
  have hfac : (0 : ℝ) ≤ ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) := by positivity
  exact mul_le_mul_of_nonneg_left hSpow hfac

/-- For every natural `n`, the real number `n + 1` is bounded by `4 * 2 ^ n`. -/
theorem natCast_add_one_le_four_mul_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h2 : (2 : ℝ) ^ k ≥ 1 := one_le_pow₀ (by norm_num)
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      nlinarith

/-- Under the shifted-parameter nonvanishing hypotheses and `T ≥ 1`, the series with terms
`‖confCoeff a b (n + 2)‖ * (n + 2) * T ^ n` is summable. -/
theorem summable_norm_confCoeff_succ_succ_mul_pow_base (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun n : ℕ => ‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) * T ^ n) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have h1 := summable_norm_confCoeff_succ_mul_pow a b ha hb T hT
  have h2 := (summable_nat_add_iff 1).2 h1
  have h3 := h2.mul_left (T⁻¹)
  refine h3.congr (fun n => ?_)
  have hidx : n + 1 + 1 = n + 2 := by omega
  rw [hidx, pow_succ]
  have hTne : T ≠ 0 := hTpos.ne'
  push_cast
  field_simp
  ring

/-- Under the shifted-parameter nonvanishing hypotheses and `S ≥ 1`, the norms of the reindexed
second-derivative terms weighted by `S ^ n` are summable. -/
theorem summable_norm_confCoeff_succ_succ_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (S : ℝ) (hS : 1 ≤ S) :
    Summable (fun n : ℕ => ‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * S ^ n) := by
  have hSpos : 0 < S := by linarith
  have hS2 : 1 ≤ 2 * S := by linarith
  have hbase := summable_norm_confCoeff_succ_succ_mul_pow_base a b ha hb (2 * S) hS2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hbase.mul_left 4)
  have hc : (0 : ℝ) ≤ ‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) := by positivity
  have hSp : (0 : ℝ) ≤ S ^ n := (pow_pos hSpos n).le
  have hle : ((n : ℝ) + 1) * S ^ n ≤ 4 * (2 * S) ^ n := by
    have h1 : (n : ℝ) + 1 ≤ 4 * 2 ^ n := natCast_add_one_le_four_mul_two_pow n
    have h2 : ((n : ℝ) + 1) * S ^ n ≤ (4 * 2 ^ n) * S ^ n :=
      mul_le_mul_of_nonneg_right h1 hSp
    have h3 : (4 * 2 ^ n) * S ^ n = 4 * (2 * S) ^ n := by rw [mul_pow]; ring
    linarith
  calc ‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * S ^ n
      = (‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2)) * (((n : ℝ) + 1) * S ^ n) := by ring
    _ ≤ (‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2)) * (4 * (2 * S) ^ n) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = 4 * (‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) * (2 * S) ^ n) := by ring

/-- Under the shifted-parameter nonvanishing hypotheses and `R ≥ 1`, the series with terms
`‖confCoeff a b n‖ * n * R ^ (n - 1)` is summable. -/
theorem summable_norm_confCoeff_nat_mul_pow_pred (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (R : ℝ) (hR : 1 ≤ R) :
    Summable (fun n : ℕ => ‖confCoeff a b n‖ * (n : ℝ) * R ^ (n - 1)) := by
  have hS : 1 ≤ 2 * (1 + R) := by linarith
  have hbase := summable_norm_confCoeff_mul_pow a b ha hb (2 * (1 + R)) (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hc : (0 : ℝ) ≤ ‖confCoeff a b n‖ := norm_nonneg _
  have hkey : (n : ℝ) * R ^ (n - 1) ≤ (2 * (1 + R)) ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hRp : R ^ (n - 1) ≤ (1 + R) ^ (n - 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (n - 1)
      have hmono : (1 + R) ^ (n - 1) ≤ (1 + R) ^ n := by
        refine pow_le_pow_right₀ (by linarith) (by omega)
      have h2 : (n : ℝ) ≤ 2 ^ n := natCast_le_two_pow n
      have h2p : (0 : ℝ) < (1 + R) ^ n := pow_pos (by linarith) n
      calc (n : ℝ) * R ^ (n - 1) ≤ (n : ℝ) * (1 + R) ^ n := by
            exact mul_le_mul_of_nonneg_left (hRp.trans hmono) (by positivity)
        _ ≤ 2 ^ n * (1 + R) ^ n := mul_le_mul_of_nonneg_right h2 h2p.le
        _ = (2 * (1 + R)) ^ n := (mul_pow 2 (1 + R) n).symm
  calc ‖confCoeff a b n‖ * (n : ℝ) * R ^ (n - 1)
      = ‖confCoeff a b n‖ * ((n : ℝ) * R ^ (n - 1)) := by ring
    _ ≤ ‖confCoeff a b n‖ * (2 * (1 + R)) ^ n := mul_le_mul_of_nonneg_left hkey hc

/-- Under the shifted-parameter nonvanishing hypotheses and `R ≥ 1`, the series with terms
`‖confCoeff a b (n + 1)‖ * (n + 1) * n * R ^ (n - 1)` is summable. -/
theorem summable_norm_confCoeff_succ_mul_pow_pred (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (R : ℝ) (hR : 1 ≤ R) :
    Summable (fun n : ℕ =>
      ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * (n : ℝ) * R ^ (n - 1)) := by
  have hS : 1 ≤ 2 * (1 + R) := by linarith
  have hbase := summable_norm_confCoeff_succ_mul_pow a b ha hb (2 * (1 + R)) hS
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hc : (0 : ℝ) ≤ ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) := by positivity
  have hkey : (n : ℝ) * R ^ (n - 1) ≤ (2 * (1 + R)) ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hRp : R ^ (n - 1) ≤ (1 + R) ^ (n - 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (n - 1)
      have hmono : (1 + R) ^ (n - 1) ≤ (1 + R) ^ n :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have h2 : (n : ℝ) ≤ 2 ^ n := natCast_le_two_pow n
      have h2p : (0 : ℝ) < (1 + R) ^ n := pow_pos (by linarith) n
      calc (n : ℝ) * R ^ (n - 1) ≤ (n : ℝ) * (1 + R) ^ n := by
            exact mul_le_mul_of_nonneg_left (hRp.trans hmono) (by positivity)
        _ ≤ 2 ^ n * (1 + R) ^ n := mul_le_mul_of_nonneg_right h2 h2p.le
        _ = (2 * (1 + R)) ^ n := (mul_pow 2 (1 + R) n).symm
  calc ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * (n : ℝ) * R ^ (n - 1)
      = (‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1)) * ((n : ℝ) * R ^ (n - 1)) := by ring
    _ ≤ (‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1)) * (2 * (1 + R)) ^ n :=
        mul_le_mul_of_nonneg_left hkey hc

/-- The complex norm of a natural number plus one equals that positive real number. -/
theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast
  ring

/-- Under the shifted-parameter nonvanishing hypotheses, the termwise derivative series of
`confHyper` is summable at every complex point. -/
theorem summable_confCoeff_deriv_mul (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ => confCoeff a b n * (n : ℂ) * z ^ (n - 1)) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ ≤ R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_nat_mul_pow_pred a b ha hb R hR1
  refine Summable.of_norm_bounded hu (fun n => ?_)
  have hnorm : ‖confCoeff a b n * (n : ℂ) * z ^ (n - 1)‖
      = ‖confCoeff a b n‖ * (n : ℝ) * ‖z‖ ^ (n - 1) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  have hle : ‖z‖ ^ (n - 1) ≤ R ^ (n - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hzR (n - 1)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Under the shifted-parameter nonvanishing hypotheses, the reindexed first-derivative series
is summable at every complex point. -/
theorem summable_confCoeff_succ_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ => confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ ≤ R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_succ_mul_pow a b ha hb R hR1
  refine Summable.of_norm_bounded hu (fun n => ?_)
  have hnorm : ‖confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n‖
      = ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * ‖z‖ ^ n := by
    rw [norm_mul, norm_mul, norm_pow, norm_natCast_add_one]
  rw [hnorm]
  have hle : ‖z‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hzR n
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Under the shifted-parameter nonvanishing hypotheses, the termwise derivative series of
`confHyperDeriv` is summable at every complex point. -/
theorem summable_confCoeff_succ_deriv_mul (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ => confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ (n - 1)) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ ≤ R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_succ_mul_pow_pred a b ha hb R hR1
  refine Summable.of_norm_bounded hu (fun n => ?_)
  have hnorm : ‖confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ (n - 1)‖
      = ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * (n : ℝ) * ‖z‖ ^ (n - 1) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_natCast_add_one, Complex.norm_natCast]
  rw [hnorm]
  have hle : ‖z‖ ^ (n - 1) ≤ R ^ (n - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hzR (n - 1)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Under the shifted-parameter nonvanishing hypotheses, the reindexed second-derivative series
is summable at every complex point. -/
theorem summable_confCoeff_succ_succ_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ => confCoeff a b (n + 2) * ((n : ℂ) + 2) * ((n : ℂ) + 1) * z ^ n) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ ≤ R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_succ_succ_mul_pow a b ha hb R hR1
  refine Summable.of_norm_bounded hu (fun n => ?_)
  have h1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := norm_natCast_add_one n
  have h2 : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by
    rw [show ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  have hnorm : ‖confCoeff a b (n + 2) * ((n : ℂ) + 2) * ((n : ℂ) + 1) * z ^ n‖
      = ‖confCoeff a b (n + 2)‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * ‖z‖ ^ n := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, h2, h1]
  rw [hnorm]
  have hle : ‖z‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hzR n
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Under the shifted-parameter nonvanishing hypotheses, `confHyperDeriv` equals the unreindexed
termwise derivative sum of `confHyper`. -/
theorem confHyperDeriv_eq_tsum (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    confHyperDeriv a b z = ∑' n : ℕ, confCoeff a b n * (n : ℂ) * z ^ (n - 1) := by
  unfold confHyperDeriv
  have hf : Summable (fun n : ℕ => confCoeff a b n * (n : ℂ) * z ^ (n - 1)) :=
    summable_confCoeff_deriv_mul a b ha hb z
  rw [hf.tsum_eq_zero_add]
  have h0 : confCoeff a b 0 * ((0 : ℕ) : ℂ) * z ^ (0 - 1) = 0 := by simp
  rw [h0, zero_add]
  refine tsum_congr (fun n => ?_)
  have he : n + 1 - 1 = n := by omega
  rw [he]
  push_cast
  ring

/-- Under the shifted-parameter nonvanishing hypotheses, `confHyperSecond` equals the
unreindexed termwise derivative sum of `confHyperDeriv`. -/
theorem confHyperSecond_eq_tsum (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    confHyperSecond a b z
      = ∑' n : ℕ, confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ (n - 1) := by
  unfold confHyperSecond
  have hf : Summable (fun n : ℕ =>
      confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ (n - 1)) :=
    summable_confCoeff_succ_deriv_mul a b ha hb z
  rw [hf.tsum_eq_zero_add]
  have h0 : confCoeff a b (0 + 1) * (((0 : ℕ) : ℂ) + 1) * ((0 : ℕ) : ℂ) * z ^ (0 - 1) = 0 :=
    by simp
  rw [h0, zero_add]
  refine tsum_congr (fun n => ?_)
  have hidx : n + 1 + 1 = n + 2 := by omega
  have he : n + 1 - 1 = n := by omega
  rw [hidx, he]
  push_cast
  ring

/-- Under the shifted-parameter nonvanishing hypotheses, `confHyper` has complex derivative
`confHyperDeriv` at every point. -/
theorem hasDerivAt_confHyper (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    HasDerivAt (confHyper a b) (confHyperDeriv a b z) z := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ < R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_nat_mul_pow_pred a b ha hb R hR1
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (g := fun n => fun w : ℂ => confCoeff a b n * w ^ n)
    (g' := fun n => fun y : ℂ => confCoeff a b n * (n : ℂ) * y ^ (n - 1))
    (u := fun n => ‖confCoeff a b n‖ * (n : ℝ) * R ^ (n - 1))
    hu Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (by
      intro n y hy
      have h := (hasDerivAt_pow n y).const_mul (confCoeff a b n)
      convert! h using 1
      ring)
    (by
      intro n y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      have hnorm : ‖confCoeff a b n * (n : ℂ) * y ^ (n - 1)‖
          = ‖confCoeff a b n‖ * (n : ℝ) * ‖y‖ ^ (n - 1) := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      rw [hnorm]
      have hle : ‖y‖ ^ (n - 1) ≤ R ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hy.le (n - 1)
      exact mul_le_mul_of_nonneg_left hle (by positivity))
    (Metric.mem_ball_self hRpos)
    (by simpa using summable_confCoeff_mul_pow a b ha hb 0)
    (by rw [Metric.mem_ball, dist_zero_right]; exact hzR)
  have hfun : (fun w : ℂ => ∑' n : ℕ, confCoeff a b n * w ^ n) = confHyper a b := by
    funext w
    rfl
  rw [hfun] at hmain
  rw [← confHyperDeriv_eq_tsum a b ha hb z] at hmain
  exact hmain

/-- Under the shifted-parameter nonvanishing hypotheses, `confHyperDeriv` has complex derivative
`confHyperSecond` at every point. -/
theorem hasDerivAt_confHyperDeriv (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    HasDerivAt (confHyperDeriv a b) (confHyperSecond a b z) z := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hzR : ‖z‖ < R := by rw [hR]; linarith
  have hu := summable_norm_confCoeff_succ_mul_pow_pred a b ha hb R hR1
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (g := fun n => fun w : ℂ => confCoeff a b (n + 1) * ((n : ℂ) + 1) * w ^ n)
    (g' := fun n => fun y : ℂ =>
      confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * y ^ (n - 1))
    (u := fun n => ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * (n : ℝ) * R ^ (n - 1))
    hu Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (by
      intro n y hy
      have h := (hasDerivAt_pow n y).const_mul (confCoeff a b (n + 1) * ((n : ℂ) + 1))
      convert! h using 1
      ring)
    (by
      intro n y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      have hnorm : ‖confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * y ^ (n - 1)‖
          = ‖confCoeff a b (n + 1)‖ * ((n : ℝ) + 1) * (n : ℝ) * ‖y‖ ^ (n - 1) := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_natCast_add_one, Complex.norm_natCast]
      rw [hnorm]
      have hle : ‖y‖ ^ (n - 1) ≤ R ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hy.le (n - 1)
      exact mul_le_mul_of_nonneg_left hle (by positivity))
    (Metric.mem_ball_self hRpos)
    (by simpa using summable_confCoeff_succ_mul_pow a b ha hb 0)
    (by rw [Metric.mem_ball, dist_zero_right]; exact hzR)
  have hfun : (fun w : ℂ => ∑' n : ℕ,
      confCoeff a b (n + 1) * ((n : ℂ) + 1) * w ^ n) = confHyperDeriv a b := by
    funext w
    rfl
  rw [hfun] at hmain
  rw [← confHyperSecond_eq_tsum a b ha hb z] at hmain
  exact hmain

/-- Under the shifted-parameter nonvanishing hypotheses, the series-defined confluent
hypergeometric function satisfies Kummer's equation `zF'' + (b - z)F' - aF = 0` at every
complex point. -/
theorem kummer_equation (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    z * deriv (deriv (confHyper a b)) z + (b - z) * deriv (confHyper a b) z
      - a * confHyper a b z = 0 := by
  have hderiv1 : deriv (confHyper a b) = confHyperDeriv a b := by
    funext w
    exact (hasDerivAt_confHyper a b ha hb w).deriv
  have hderiv2 : deriv (deriv (confHyper a b)) z = confHyperSecond a b z := by
    rw [hderiv1]
    exact (hasDerivAt_confHyperDeriv a b ha hb z).deriv
  have hF : HasSum (fun n : ℕ => confCoeff a b n * z ^ n) (confHyper a b z) :=
    (summable_confCoeff_mul_pow a b ha hb z).hasSum
  have hD1 : HasSum (fun n : ℕ => confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n)
      (confHyperDeriv a b z) := (summable_confCoeff_succ_mul_pow a b ha hb z).hasSum
  have hD2 : HasSum
      (fun n : ℕ => confCoeff a b (n + 2) * ((n : ℂ) + 2) * ((n : ℂ) + 1) * z ^ n)
      (confHyperSecond a b z) := (summable_confCoeff_succ_succ_mul_pow a b ha hb z).hasSum

  have hE : HasSum
      (fun n : ℕ => confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ n)
      (z * confHyperSecond a b z) := by
    let E : ℕ → ℂ := fun m => confCoeff a b (m + 1) * ((m : ℂ) + 1) * (m : ℂ) * z ^ m
    have hshift : HasSum (fun n => E (n + 1)) (z * confHyperSecond a b z) :=
      (hD2.mul_left z).congr_fun (g := fun n => E (n + 1)) (fun n => by
        have hidx : n + 1 + 1 = n + 2 := by omega
        dsimp [E]
        rw [hidx, pow_succ]
        push_cast
        ring)
    have hE0 : E 0 = 0 := by dsimp [E]; simp
    have hres := HasSum.zero_add hshift
    rw [hE0, zero_add] at hres
    simpa [E] using hres

  have hA : HasSum (fun n : ℕ => confCoeff a b n * (n : ℂ) * z ^ n)
      (z * confHyperDeriv a b z) := by
    let A : ℕ → ℂ := fun m => confCoeff a b m * (m : ℂ) * z ^ m
    have hshift : HasSum (fun n => A (n + 1)) (z * confHyperDeriv a b z) :=
      (hD1.mul_left z).congr_fun (g := fun n => A (n + 1)) (fun n => by
        dsimp [A]
        rw [pow_succ]
        push_cast
        ring)
    have hA0 : A 0 = 0 := by dsimp [A]; simp
    have hres := HasSum.zero_add hshift
    rw [hA0, zero_add] at hres
    simpa [A] using hres
  have hcomb := (hE.add (hD1.mul_left b)).sub hA |>.sub (hF.mul_left a)
  have hterm : ∀ n : ℕ,
      confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ n
        + b * (confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n)
        - confCoeff a b n * (n : ℂ) * z ^ n
        - a * (confCoeff a b n * z ^ n) = 0 := by
    intro n
    have hkey : confCoeff a b (n + 1) * ((n : ℂ) + 1) * ((n : ℂ) + b)
        = confCoeff a b n * ((n : ℂ) + a) := by
      have hrec := confCoeff_succ_mul a b n (hb n)
      linear_combination -hrec
    calc confCoeff a b (n + 1) * ((n : ℂ) + 1) * (n : ℂ) * z ^ n
          + b * (confCoeff a b (n + 1) * ((n : ℂ) + 1) * z ^ n)
          - confCoeff a b n * (n : ℂ) * z ^ n
          - a * (confCoeff a b n * z ^ n)
          = z ^ n * (confCoeff a b (n + 1) * ((n : ℂ) + 1) * ((n : ℂ) + b)
              - confCoeff a b n * ((n : ℂ) + a)) := by ring
      _ = 0 := by rw [hkey]; ring
  have hzero : HasSum (fun _ : ℕ => (0 : ℂ))
      (z * confHyperSecond a b z + b * confHyperDeriv a b z
        - z * confHyperDeriv a b z - a * confHyper a b z) :=
    hcomb.congr_fun (fun n => (hterm n).symm)
  have hV : z * confHyperSecond a b z + b * confHyperDeriv a b z
      - z * confHyperDeriv a b z - a * confHyper a b z = 0 :=
    hzero.unique hasSum_zero
  rw [hderiv2, hderiv1]
  linear_combination hV

end Qatlib.Foundations.SpecialFuncs.KummerODE
