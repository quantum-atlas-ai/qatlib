/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic rates for finite moments

This module extracts the constant, logarithmic, and power growth regimes of finite uniform-grid
coefficient moments. The piecewise `rate` sharpens `momentGrowth` as the Gaussian scale tends to
infinity, for the quadrature analysis associated with [AftabAnTrivisa2026].

## Main statements

* `growth_le_rate`: domination of the moment growth factor by its asymptotic rate.
* `finite_moment_isBigO`: the resulting finite-moment asymptotic bound.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.MomentRates
open Filter Set Asymptotics
open scoped Topology BigOperators
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments

/-- The piecewise moment rate: one below `ν = n`, `log (1 + c)` at equality, and `c^(ν - n)`
above equality. -/
def rate (n : ℕ) (ν c : ℝ) : ℝ :=
  if ν < n then 1 else if ν = n then Real.log (1 + c) else c ^ (ν - n)

/-- The piecewise moment rate is positive for `c ≥ 1`. -/
theorem rate_pos (n : ℕ) (ν : ℝ) {c : ℝ} (hc : 1 ≤ c) : 0 < rate n ν c := by
  unfold rate
  split_ifs
  · norm_num
  · exact Real.log_pos (by linarith)
  · exact Real.rpow_pos_of_pos (by linarith) _

/-- The growth function `momentGrowth` is bounded by a positive constant times `rate` uniformly
for `c ≥ 1`. -/
theorem growth_le_rate (n : ℕ) (ν : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 1 ≤ c → momentGrowth n ν c ≤ D * rate n ν c := by
  let D := max 2 (1 + 1 / Real.log 2)
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨D, hD, fun c hc => ?_⟩
  unfold momentGrowth rate
  split_ifs with hn he
  · simpa only [mul_one] using! (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _))
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log (1 + c) := Real.log_le_log (by norm_num) (by linarith)
    have hlog : 0 ≤ Real.log (1 + c) := by linarith
    have hm : 1 ≤ Real.log (1 + c) / Real.log 2 := (le_div_iff₀ h2).mpr (by simpa)
    calc
      _ ≤ Real.log (1 + c) / Real.log 2 + Real.log (1 + c) := by linarith
      _ = (1 + 1 / Real.log 2) * Real.log (1 + c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
  · have hp : 0 < ν - n := sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he))
    have hpow : 1 ≤ c ^ (ν - n) := Real.one_le_rpow hc hp.le
    calc
      _ ≤ 2 * c ^ (ν - n) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- For fixed positive `b` and nonnegative moment order, finite quadrature moments are
`O(kernelScale * rate)` as `c` tends to infinity when the mesh step is eventually in `(0,
1]`; see [AftabAnTrivisa2026]. -/
theorem finite_moment_isBigO (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν)
    (d h R : ℝ → ℝ) (hh : ∀ᶠ c : ℝ in atTop, 0 < h c)
    (hh1 : ∀ᶠ c : ℝ in atTop, h c ≤ 1) :
    (fun c : ℝ => ∑ q ∈ Finset.Icc (-(cutoff (R c) (h c) : ℤ)) (cutoff (R c) (h c) : ℤ),
      ‖((h c : ℝ) : ℂ) * coefficient n b c (d c) (((h c) * (q : ℝ) : ℝ) : ℂ)‖ *
        |(h c) * (q : ℝ)| ^ ν) =O[atTop]
      (fun c => kernelScale n b c (d c) * rate n ν c) := by
  obtain ⟨C, hC, hm⟩ := finite_rule_moments n b ν hb hν
  obtain ⟨D, hD, hrate⟩ := growth_le_rate n ν
  apply IsBigO.of_bound (C * D)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hh, hh1] with c hc hhc hhc1
  have hc0 : 0 < c := by linarith
  have hs : 0 ≤ kernelScale n b c (d c) * C := by unfold kernelScale; positivity
  have hf0 : 0 ≤ ∑ q ∈ Finset.Icc (-(cutoff (R c) (h c) : ℤ)) (cutoff (R c) (h c) : ℤ),
      ‖((h c : ℝ) : ℂ) * coefficient n b c (d c) (((h c) * (q : ℝ) : ℝ) : ℂ)‖ *
        |(h c) * (q : ℝ)| ^ ν := by positivity
  have hg0 : 0 ≤ kernelScale n b c (d c) * rate n ν c := by
    exact mul_nonneg (by unfold kernelScale; positivity) (rate_pos n ν hc).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hg0]
  calc
    _ ≤ kernelScale n b c (d c) * C * momentGrowth n ν c := hm c hc0 (d c) (h c) hhc hhc1 (R c)
    _ ≤ kernelScale n b c (d c) * C * (D * rate n ν c) := mul_le_mul_of_nonneg_left (hrate c hc) hs
    _ = _ := by ring

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.MomentRates
