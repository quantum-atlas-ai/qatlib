/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Classical sampling at high marked density

This module treats classical sampling when the marked density exceeds three quarters. It proves
that the geometric first-success expectation is N/t < 4/3 and that the probability of k
consecutive failures is at most (1/4)ᵏ.

The source paper is [BoyerEtAl1998].

## Main statements

* `classical_sampling_constant_expected_time`: For 0 < N and 3N/4 < t ≤ N, the geometric
  first-success expectation sums to N/t < 4/3, and the k-failure factor is at most (1/4)ᵏ for
  every k.
* `classical_sampling_expected_probes_lt_four_thirds`: For positive N and t > 3N/4, the ratio
  N/t is strictly less than 4/3.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchBoyer98.MainResults

/-- For 0 < N and 3N/4 < t ≤ N, the geometric first-success expectation sums to N/t < 4/3, and
the k-failure factor is at most (1/4)ᵏ for every k [BoyerEtAl1998]. -/
theorem classical_sampling_constant_expected_time (N t : ℕ) (hN : 0 < N)
    (hdense : 3 * (N : ℝ) / 4 < t) (htN : t ≤ N) :
    HasSum (fun k : ℕ => (1 - (t : ℝ) / N) ^ k * ((t : ℝ) / N) * ((k : ℝ) + 1))
        ((N : ℝ) / t) ∧
      (N : ℝ) / t < 4 / 3 ∧
      ∀ k : ℕ, (1 - (t : ℝ) / N) ^ k ≤ (1 / 4 : ℝ) ^ k := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have : (0 : ℝ) < 3 * (N : ℝ) / 4 := by positivity
    linarith
  have htN' : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
  set p : ℝ := (t : ℝ) / N with hp
  have hp_pos : 0 < p := by rw [hp]; positivity
  set q : ℝ := 1 - p with hq
  have hq_nonneg : 0 ≤ q := by
    rw [hq, hp, sub_nonneg, div_le_one hNpos]
    exact htN'
  have hq_lt_one : q < 1 := by rw [hq]; linarith
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]; exact hq_lt_one
  refine ⟨?_, ?_, ?_⟩
  · have hgeo := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hq_norm).add
      (hasSum_geometric_of_norm_lt_one (K := ℝ) hq_norm)
    have hmul := hgeo.mul_left p
    have hq' : q = 1 - (t : ℝ) / N := by rw [hq, hp]
    have hval : p * (q / (1 - q) ^ 2 + (1 - q)⁻¹) = (N : ℝ) / t := by
      rw [hq', hp, show 1 - (1 - (t : ℝ) / N) = (t : ℝ) / N by ring]
      field_simp
      ring
    rw [← hval]
    convert! hmul using 1
    ext k
    ring
  · rw [div_lt_iff₀ htpos]
    linarith
  · intro k
    have hq_le : q ≤ 1 / 4 := by
      have : 3 / 4 < (t : ℝ) / N := by
        rw [lt_div_iff₀ hNpos]
        linarith
      rw [hq, hp]; linarith
    simpa [hq, hp] using pow_le_pow_left₀ hq_nonneg hq_le k

/-- For positive N and t > 3N/4, the ratio N/t is strictly less than 4/3. -/
theorem classical_sampling_expected_probes_lt_four_thirds (N t : ℕ) (hN : 0 < N)
    (hdense : 3 * (N : ℝ) / 4 < t) : (N : ℝ) / t < 4 / 3 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have : (0 : ℝ) < 3 * (N : ℝ) / 4 := by positivity
    linarith
  rw [div_lt_iff₀ htpos]
  linarith

end Qatlib.Papers.QSearchBoyer98.MainResults
