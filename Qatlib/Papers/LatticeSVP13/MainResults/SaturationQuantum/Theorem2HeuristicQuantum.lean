/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeSVP13.MainResults.SaturationQuantum.Lemma6QuantumSaturation

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2: optimal quantum saturation constants

Laarhoven--Mosca--van de Pol, fixed arXiv:1301.6176v1 (25 Jan 2013), Theorem 2, p. 9,
and Appendix B, p. 17.

> **Theorem 2.** Let `ξ ≈ 0.9086` and `R ≈ 3.1376`.  Then, using polynomially many
> queries to the quantum version of Algorithm 2, we can find a shortest vector in a
> lattice with probability exponentially close to `1`, using time at most
> `2 ^ (1.799 n + o(n))` and space at most `2 ^ (1.286 n + o(n))`.

Lemma 6 gives time exponent `t̃(ξ, R)` and space exponent `s̃(ξ, R)` for general `ξ, R`
(Equation (7)); evaluating at `ξ = 0.9086`, `R = 3.1376` and bounding the constants of
Equations (2)–(4) yields `t̃ ≤ 1.799` and `s̃ ≤ 1.286`.  The space bound is tight (the
true value is about `1.2856`), so it is proved here with sharper Taylor bounds than the
time bound: `log₂(4ξ²/(4ξ²-1)) ≤ 0.5208` and `log₂ R ≤ 1.650`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.SaturationQuantum

open Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

/-! ## The tight numerical bounds needed for the space exponent -/

/-- `c_g(0.9086) ≤ 0.2604`, i.e. `log₂(4ξ²/(4ξ²-1)) ≤ 0.5208` at `ξ = 0.9086`. -/
theorem cG_09086_le_tight : cG 0.9086 ≤ 0.2604 := by
  have hlog : Real.logb 2 (4 * (0.9086 : ℝ) ^ 2 / (4 * (0.9086 : ℝ) ^ 2 - 1)) ≤ 0.5208 := by
    apply logb_two_le_of_taylor
      (x := 4 * (0.9086 : ℝ) ^ 2 / (4 * (0.9086 : ℝ) ^ 2 - 1))
      (y := 0.5208) (z := 0.5208 * 0.6931471803) (n := 12)
    · norm_num
    · norm_num
    · nlinarith [Real.log_two_gt_d9]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold cG
  nlinarith [hlog]

/-- `c_b(3.1376) ≤ 2.051`, i.e. `log₂(3.1376) ≤ 1.650`. -/
theorem cB_31376_le_tight : cB 3.1376 ≤ 2.051 := by
  have hlog : Real.logb 2 (3.1376 : ℝ) ≤ 1.650 := by
    apply logb_two_le_of_taylor (x := 3.1376) (y := 1.650)
      (z := 1.650 * 0.6931471803) (n := 11)
    · norm_num
    · norm_num
    · nlinarith [Real.log_two_gt_d9]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold cB
  nlinarith [hlog]

/-- `t̃(0.9086, 3.1376) ≤ 1.799` (Equation (7)). -/
theorem theorem2_time_exponent_le :
    quantumTimeExponent (cB 3.1376) (cT 0.9086 3.1376) (cG 0.9086) ≤ 1.799 := by
  unfold quantumTimeExponent
  have hcg := cG_09086_le
  have hct := cT_09086_31376_le
  have hcb := cB_31376_le
  have hd1 : cG 0.9086 + 3 * cT 0.9086 3.1376 / 2 ≤ 1.799 := by nlinarith [hcg, hct]
  have hd2 : cG 0.9086 + cB 3.1376 / 2 + cT 0.9086 3.1376 / 2 ≤ 1.799 := by
    nlinarith [hcg, hct, hcb]
  have hd3 : cG 0.9086 + cB 3.1376 / 2 ≤ 1.799 := by nlinarith [hcg, hcb]
  exact max_le (max_le hd1 hd2) hd3

/-- `s̃(0.9086, 3.1376) ≤ 1.286` (Equation (7)).  Tight: the true value is about
`1.2856`, so the sharper bounds `c_g ≤ 0.2604`, `c_b ≤ 2.051` are used. -/
theorem theorem2_space_exponent_le :
    quantumSpaceExponent (cB 3.1376) (cT 0.9086 3.1376) (cG 0.9086) ≤ 1.286 := by
  unfold quantumSpaceExponent
  have hcg := cG_09086_le_tight
  have hct := cT_09086_31376_le
  have hcb := cB_31376_le_tight
  have hspace : cG 0.9086 + cB 3.1376 / 2 ≤ 1.286 := by nlinarith [hcg, hcb]
  exact max_le (by nlinarith [hct]) hspace

/-- **Theorem 2** (arXiv:1301.6176v1, p. 9).  With `ξ = 0.9086`, `R = 3.1376`, the
quantum saturation algorithm has time exponent `≤ 1.799` and space exponent `≤ 1.286`.

This composes Lemma 6 (`lemma6_quantum_saturation`) with the numeric bounds above.  The
`probability exponentially close to 1` and `find a shortest vector` clauses are the
correctness inputs of [44] (via Heuristic 1 / Lemma 6's `1/16` amplification);
`finding a shortest vector with high probability` is not re-derived here. -/
theorem theorem2_quantum_saturation
    (Tgen Sgen Ssearch time space : ℕ → ℝ)
    (hTgen : HasLog2Exponent (fun n => Real.logb 2 (Tgen n))
      (cG 0.9086 + 3 * cT 0.9086 3.1376 / 2))
    (hSgen : HasLog2Exponent (fun n => Real.logb 2 (Sgen n))
      (cG 0.9086 + cB 3.1376 / 2 + cT 0.9086 3.1376 / 2))
    (hSsearch : HasLog2Exponent (fun n => Real.logb 2 (Ssearch n))
      (cG 0.9086 + cB 3.1376 / 2))
    (hSpace : HasLog2Exponent (fun n => Real.logb 2 (space n))
      (quantumSpaceExponent (cB 3.1376) (cT 0.9086 3.1376) (cG 0.9086)))
    (hTime : ∀ n, time n = Tgen n + Sgen n + Ssearch n)
    (hpTgen : ∀ n, 0 < Tgen n) (hpSgen : ∀ n, 0 < Sgen n) (hpSsearch : ∀ n, 0 < Ssearch n) :
    HasLog2Exponent (fun n => Real.logb 2 (time n)) 1.799 ∧
    HasLog2Exponent (fun n => Real.logb 2 (space n)) 1.286 := by
  have h6 := lemma6_quantum_saturation 0.9086 3.1376 (by norm_num) (by norm_num)
    Tgen Sgen Ssearch time space hTgen hSgen hSsearch hSpace hTime hpTgen hpSgen hpSsearch
  exact ⟨h6.1.mono_coeff theorem2_time_exponent_le,
    h6.2.mono_coeff theorem2_space_exponent_le⟩

end Qatlib.Papers.LatticeSVP13.MainResults.SaturationQuantum
