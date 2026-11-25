/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling.SourceFourierSampling
public import Qatlib.Papers.LinFuncSubset18.MainResults.Core.SourceCore
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Fourier-sampling repetition and time

The displayed estimate before Corollary 4.2 of arXiv:1806.09660v1 requires
an upper bound on the gap `1 - r/q`. The printed lower bound on that gap
also permits `r/q = 1/2`, for which the stated repetition factor is exponential.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology
open Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling
open Qatlib.Papers.LinFuncSubset18.MainResults.Core

namespace Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling

/-- The reciprocal sampling factor has a uniform polynomial bound for every fixed additive
offset `k` and fixed upper-bound constant `c`. -/
theorem corollary4_2_time_bound {q r n k : ℕ} (hr : 0 < r) (hrq : r ≤ q) (hn : 2 ≤ n)
    {c : ℝ}
    (hsmall : 1 - (r : ℝ) / q ≤ 1 / 2)
    (hgap : 1 - (r : ℝ) / q ≤ c * Real.log n / n) :
    ((q : ℝ) / r) ^ (n + k) ≤ (n : ℝ) ^ (2 * (c * ((k : ℝ) + 1))) := by
  let δ := 1 - (r : ℝ) / q
  have hq : (0 : ℝ) < q := by exact_mod_cast (hr.trans_le hrq)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr ((div_le_one hq).mpr (by exact_mod_cast hrq))
  have hδn : δ * (n : ℝ) ≤ c * Real.log n := (le_div_iff₀ hn0).mp hgap
  have hk : (n : ℝ) + k ≤ (n : ℝ) * ((k : ℝ) + 1) := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) (sub_nonneg.mpr hn1)]
  have hb : δ * ((n : ℝ) + k) ≤ (c * ((k : ℝ) + 1)) * Real.log n := by
    calc
      _ ≤ δ * ((n : ℝ) * ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hk hδ0
      _ = (δ * (n : ℝ)) * ((k : ℝ) + 1) := by ring
      _ ≤ (c * Real.log n) * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_right hδn (by positivity)
      _ = _ := by ring
  have hrestore : 1 - δ = (r : ℝ) / q := by dsimp only [δ]; ring
  have hpos : 0 < 1 - δ := by rw [hrestore]; exact div_pos (by exact_mod_cast hr) hq
  calc
    _ = Real.exp (((n : ℝ) + k) * (-Real.log (1 - δ))) := by
      rw [← Nat.cast_add, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpos, hrestore, inv_div]
    _ ≤ _ := geometric_decay_bound hn hδ0 hsmall hb

/-- At fixed `c`, the upper-gap hypothesis itself implies the half-gap bound eventually. -/
theorem eventually_log_gap_le_half (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * Real.log (n : ℝ) / (n : ℝ) ≤ 1 / 2 := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn).const_mul c
  have ht : Tendsto (fun n : ℕ => c * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_zero, mul_div_assoc] using hlog
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hf
  exact (show c * Real.log (n : ℝ) / (n : ℝ) < 1 / 2 from hf).le

/-- Combining the published polynomial trial template with the repetition factor retains
its explicit logarithmic dependence on the modulus. -/
theorem fourierSampling_time_bound {q r n k d C : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (hn : 2 ≤ n) {c : ℝ}
    (hsmall : 1 - (r : ℝ) / q ≤ 1 / 2)
    (hgap : 1 - (r : ℝ) / q ≤ c * Real.log n / n) :
    (polyTimeBudget q n d C : ℝ) * ((q : ℝ) / r) ^ (n + k) ≤
      (C : ℝ) * (2 : ℝ) ^ d * ((Nat.log 2 q + 1 : ℕ) : ℝ) ^ d *
        (n : ℝ) ^ ((d : ℝ) + 2 * (c * ((k : ℝ) + 1))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : ((n : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ d * (n : ℝ) ^ d := by
    rw [← mul_pow]
    gcongr
    linarith
  have hrep := corollary4_2_time_bound (k := k) hr hrq hn hsmall hgap
  unfold polyTimeBudget
  push_cast
  calc
    _ ≤ (C : ℝ) * ((2 : ℝ) ^ d * (n : ℝ) ^ d) * ((Nat.log 2 q : ℝ) + 1) ^ d *
          (n : ℝ) ^ (2 * (c * ((k : ℝ) + 1))) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_add (by linarith : (0 : ℝ) < n), Real.rpow_natCast]
      ring

/-- The full template bound holds beyond a cutoff depending only on the gap constant,
uniformly in the valid modulus and subset sizes and for any fixed polynomial parameters. -/
theorem eventually_fourierSampling_time_bound (c : ℝ) (k d C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q r : ℕ, 0 < r → r ≤ q →
      1 - (r : ℝ) / q ≤ c * Real.log n / n →
      (polyTimeBudget q n d C : ℝ) * ((q : ℝ) / r) ^ (n + k) ≤
        (C : ℝ) * (2 : ℝ) ^ d * ((Nat.log 2 q + 1 : ℕ) : ℝ) ^ d *
          (n : ℝ) ^ ((d : ℝ) + 2 * (c * ((k : ℝ) + 1))) := by
  filter_upwards [eventually_log_gap_le_half c, eventually_ge_atTop (2 : ℕ)] with n hsmall hn
  intro q r hr hrq hgap
  exact fourierSampling_time_bound hr hrq hn (hgap.trans hsmall) hgap

/-- A gap of one half satisfies a lower bound of order `log n / n`. -/
theorem half_gap_satisfies_printed_lower_bound {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) * (Real.log n / n) ≤ 1 - (1 : ℝ) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n : ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hdiv := (div_le_one hn0).mpr hlog
  linarith

/-- At `q=2, r=1`, the stated repetition factor has no eventual polynomial upper bound. -/
theorem half_gap_repetition_not_polynomial (C : ℝ) (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ n ≤ C * (n : ℝ) ^ d) := by
  intro h
  have hr := (tendsto_pow_const_div_const_pow_of_one_lt d
    (r := (2 : ℝ)) (by norm_num)).const_mul C
  have ht : Tendsto (fun n : ℕ => C * ((n : ℝ) ^ d / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr
  have hs := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [h, hs] with n hlo hhi
    have hpos : 0 < (2 : ℝ) ^ n := by positivity
    have hge : 1 ≤ C * ((n : ℝ) ^ d / (2 : ℝ) ^ n) := by
      rw [← mul_div_assoc, le_div_iff₀ hpos, one_mul]
      exact hlo
    exact (not_lt_of_ge hge) (show C * ((n : ℝ) ^ d / (2 : ℝ) ^ n) < 1 from hhi)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hfalse
  exact hn n le_rfl

end Qatlib.Papers.LinFuncSubset18.MainResults.FourierSampling
