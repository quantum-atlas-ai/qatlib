/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.MarkedCombine
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

theorem verify_steps_bound {δ ε n k q C D : ℝ}
    (hn : 0 < n) (hk : 0 < k) (hq : 0 < q) (hC : 0 < C) (hD : 0 < D)
    (hδ : D / k ≤ δ) (hε : C * k ^ 2 * q / n ^ 2 ≤ ε) :
    1 / Real.sqrt (δ * ε) ≤ n / Real.sqrt (C * D * k * q) := by
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hkq : (0 : ℝ) < k * q := mul_pos hk hq
  have hCDkq : (0 : ℝ) < C * D * k * q := by positivity

  have hδε : C * D * k * q / n ^ 2 ≤ δ * ε := by
    have hδ0 : (0 : ℝ) ≤ δ := le_trans (by positivity : (0 : ℝ) ≤ D / k) hδ
    have h1 : (D / k) * (C * k ^ 2 * q / n ^ 2) ≤ δ * ε :=
      mul_le_mul hδ hε (by positivity) hδ0
    have heq : (D / k) * (C * k ^ 2 * q / n ^ 2) = C * D * k * q / n ^ 2 := by
      field_simp
    rwa [heq] at h1
  have hroot : Real.sqrt (C * D * k * q / n ^ 2) ≤ Real.sqrt (δ * ε) :=
    Real.sqrt_le_sqrt hδε
  have hsqrt_div : Real.sqrt (C * D * k * q / n ^ 2)
      = Real.sqrt (C * D * k * q) / n := by
    rw [Real.sqrt_div hCDkq.le, Real.sqrt_sq hn.le]
  rw [hsqrt_div] at hroot
  have hpos : 0 < Real.sqrt (C * D * k * q) / n := by positivity
  have hstep : 1 / Real.sqrt (δ * ε) ≤ 1 / (Real.sqrt (C * D * k * q) / n) :=
    one_div_le_one_div_of_le hpos hroot
  rwa [one_div_div] at hstep

theorem k0_threshold {n q k : ℝ} (hn : 0 < n) (hq : 0 < q) (hk : 0 < k)
    (h : n ^ 2 / q ≤ k ^ 3) : n / Real.sqrt (k * q) ≤ k := by
  have hkq : (0 : ℝ) < k * q := mul_pos hk hq
  have hn2 : n ^ 2 ≤ k ^ 3 * q := by
    rw [div_le_iff₀ hq] at h
    linarith
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hkq)]
  have hsq : n ^ 2 ≤ k ^ 2 * (k * q) := by nlinarith
  have hroot : Real.sqrt (n ^ 2) ≤ Real.sqrt (k ^ 2 * (k * q)) :=
    Real.sqrt_le_sqrt hsq
  have hleft : Real.sqrt (n ^ 2) = n := Real.sqrt_sq hn.le
  have hright : Real.sqrt (k ^ 2 * (k * q)) = k * Real.sqrt (k * q) := by
    rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
  rwa [hleft, hright] at hroot

theorem theorem6_time_core {δ ε n k q C D : ℝ}
    (hn : 0 < n) (hk : 0 < k) (hq : 0 < q) (hC : 0 < C) (hD : 0 < D)
    (hδ : D / k ≤ δ) (hε : C * k ^ 2 * q / n ^ 2 ≤ ε)
    (hth : n ^ 2 / q ≤ k ^ 3) :
    1 / Real.sqrt (δ * ε) ≤ k / Real.sqrt (C * D) := by
  have h1 := verify_steps_bound hn hk hq hC hD hδ hε
  have h2 := k0_threshold hn hq hk hth
  have hCD : (0 : ℝ) < C * D := by positivity
  have hsplit : n / Real.sqrt (C * D * k * q)
      = (1 / Real.sqrt (C * D)) * (n / Real.sqrt (k * q)) := by
    have harg : C * D * k * q = (C * D) * (k * q) := by ring
    rw [harg, Real.sqrt_mul hCD.le]
    field_simp
  calc 1 / Real.sqrt (δ * ε) ≤ n / Real.sqrt (C * D * k * q) := h1
    _ = (1 / Real.sqrt (C * D)) * (n / Real.sqrt (k * q)) := hsplit
    _ ≤ (1 / Real.sqrt (C * D)) * k := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
    _ = k / Real.sqrt (C * D) := by ring

theorem geom_partial_sum_le {a r : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, a * r ^ i) ≤ a / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  have hgm : (∑ i ∈ Finset.range N, r ^ i) * (1 - r) = 1 - r ^ N := by
    have h := geom_sum_mul (x := r) (n := N)
    linear_combination -h
  have hpow : 0 ≤ r ^ N := pow_nonneg hr0 N
  have hsum : (∑ i ∈ Finset.range N, r ^ i) = (1 - r ^ N) / (1 - r) := by
    rw [eq_div_iff hpos.ne']
    linarith
  calc (∑ i ∈ Finset.range N, a * r ^ i)
      = a * ∑ i ∈ Finset.range N, r ^ i := by rw [Finset.mul_sum]
    _ = a * ((1 - r ^ N) / (1 - r)) := by rw [hsum]
    _ ≤ a * (1 / (1 - r)) := by
        refine mul_le_mul_of_nonneg_left ?_ ha
        have hnum : 1 - r ^ N ≤ 1 := by linarith
        exact div_le_div_of_nonneg_right hnum hpos.le
    _ = a / (1 - r) := by ring

end Qatlib.Papers.MatProdVerify04.MainResults
