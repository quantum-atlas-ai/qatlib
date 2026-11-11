/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyDepthConvergenceRateStat

/-!
# Polynomial readout convergence rates

This module bounds the arcsine truncation tail by its zero-order value and proves
`riskPolyDepthConvergenceRate`. The result chooses rotation scale, amplitude-estimation size,
and decoding precision to achieve a prescribed readout error.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `riskPolyDepthConvergenceRate`: For every order `u` and `0 < ε ≤ 1`, polynomial readout
  parameters achieve error at most `ε` with `M ≤ 8 * π * ε ^ (-(2 * u + 3) / (2 * u + 2))`; see
  [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.RiskEstimation.PolyReadout

open scoped BigOperators

/-- The arcsine tail at any truncation order is at most `π / 2 - 1`. -/
theorem riskArcsinTail_le_zero_order (u : ℕ) : riskArcsinTail u ≤ Real.pi / 2 - 1 := by
  have hp (j : ℕ) : 0 ≤ riskArcsinCoeff j := by unfold riskArcsinCoeff; positivity
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (u + 1)) => hp j)
    (show 0 ∈ Finset.range (u + 1) by simp)
  rw [show riskArcsinCoeff 0 = 1 by simp [riskArcsinCoeff]] at hs
  unfold riskArcsinTail
  linarith

/-- For every order `u` and `0 < ε ≤ 1`, polynomial readout parameters achieve error at most `ε`
with `M ≤ 8 * π * ε ^ (-(2 * u + 3) / (2 * u + 2))`; see [WoernerEgger2019]. -/
theorem riskPolyDepthConvergenceRate : PolyDepthConvergenceRate := by
  intro u ε hε hε1
  let α : ℝ := 1 / (2 * u + 2)
  let k : ℝ := (2 * u + 3) / (2 * u + 2)
  let c := ε ^ α
  let M := Nat.ceil (4 * Real.pi / (ε * c))
  have hN : (0 : ℝ) < 2 * u + 2 := by positivity
  have hα : 0 < α := div_pos (by norm_num) hN
  have hc : 0 < c := Real.rpow_pos_of_pos hε α
  have hc1 : c ≤ 1 := Real.rpow_le_one hε.le hε1 hα.le
  have hep : 0 < ε * c := mul_pos hε hc
  have hep1 : ε * c ≤ 1 := (mul_le_mul hε1 hc1 hc.le (by norm_num)).trans_eq (one_mul _)
  have hepower : ε * c = ε ^ k := by
    calc
      _ = ε ^ (1 : ℝ) * ε ^ α := by rw [Real.rpow_one]
      _ = ε ^ (1 + α) := (Real.rpow_add hε _ _).symm
      _ = _ := by congr 1; dsimp [k, α]; field_simp; ring
  have hcpower : c ^ (2 * u + 2) = ε := by
    dsimp only [c]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    have he : α * ((2 * u + 2 : ℕ) : ℝ) = 1 := by
      dsimp [α]
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  have hceil : 4 * Real.pi / (ε * c) ≤ (M : ℝ) := Nat.le_ceil _
  have hmin : (2 : ℝ) ≤ 4 * Real.pi / (ε * c) := by
    apply (le_div_iff₀ hep).mpr
    nlinarith [Real.pi_gt_three]
  have hM : 2 ≤ M := by exact_mod_cast hmin.trans hceil
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hP : Real.pi / M ≤ ε * c / 4 := by
    apply (div_le_iff₀ hMp).mpr
    have hh := (div_le_iff₀ hep).mp hceil
    nlinarith
  have hP2 : Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ ε * c / 16 := by
    have hs := pow_le_pow_left₀ (div_nonneg Real.pi_pos.le hMp.le) hP 2
    rw [div_pow, div_pow] at hs
    norm_num at hs
    nlinarith
  obtain ⟨bits, hbits⟩ := exists_pow_lt_of_lt_one
    (by positivity : (0 : ℝ) < ε * c / 8) (by norm_num : (1 / 2 : ℝ) < 1)
  have herr : Real.pi / M + Real.pi ^ 2 / (M : ℝ) ^ 2 + (1 / 2 : ℝ) ^ bits ≤ ε * c / 2 := by
    linarith
  have hscale : (Real.pi / M + Real.pi ^ 2 / (M : ℝ) ^ 2 + (1 / 2 : ℝ) ^ bits) / c ≤ ε / 2 := by
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have htail : riskArcsinTail u ≤ 1 := by
    have hh := riskArcsinTail_le_zero_order u
    linarith [Real.pi_lt_four]
  have hwindow : riskPolyReadoutWindow u c M bits ≤ ε := by
    unfold riskPolyReadoutWindow
    rw [hcpower]
    nlinarith
  have hceilup : (M : ℝ) ≤ 4 * Real.pi / (ε * c) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hrate : (M : ℝ) ≤ 8 * Real.pi * ε ^ (-k) := by
    have hb : (M : ℝ) ≤ 8 * Real.pi / (ε * c) := by
      have he : 8 * Real.pi / (ε * c) = 2 * (4 * Real.pi / (ε * c)) := by ring
      rw [he]
      linarith
    rw [hepower, div_eq_mul_inv, ← Real.rpow_neg hε.le] at hb
    exact hb
  exact ⟨c, M, bits, hc, hc1, hM, hwindow, hrate⟩

end Qatlib.Concepts.RiskEstimation.PolyReadout
