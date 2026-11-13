/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.TanDensityPrefactorInequalityStat

/-!
# Bounds for the tangent density prefactor

`tanDensityPrefactorInequality_answer` bounds the product of the squared tangent density factor
and the rounded Grover gain. It also proves the exact tangent-density identity and positivity of
the gain under the half-density assumptions used in [Cornwell2014].

## Main statements

* `tanDensityPrefactorInequality_answer`: Proves the upper and lower bounds for tan²θ times the
  gain, the identity tan²θ = T/(N−T), and 0 < gain ≤ 1 for 2 ≤ T and 2T ≤ N; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

/-- Proves the upper and lower bounds for tan²θ times the gain, the identity tan²θ = T/(N−T),
and 0 < gain ≤ 1 for 2 ≤ T and 2T ≤ N; see [Cornwell2014]. -/
theorem tanDensityPrefactorInequality_answer : TanDensityPrefactorInequality := by
  intro N T hN hT hhalf
  (try dsimp only)
  have ht := aq_tan_density N T hN (by omega) hhalf
  have hg := amplified_progression_zero_mode_and_corrected_floor_bounds N hN 0 T 1
    hT (by decide) (by omega) hhalf
  have hp : ((T : ℝ) / (N : ℝ)) * ((N : ℝ) / ((N - T : ℕ) : ℝ)) =
      (T : ℝ) / ((N - T : ℕ) : ℝ) := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  rw [hp, ht]
  have hnonneg : 0 ≤ (T : ℝ) / ((N - T : ℕ) : ℝ) := by positivity
  exact ⟨by simpa [aqGain] using mul_le_mul_of_nonneg_left hg.2.2.2.1 hnonneg,
    by simpa [aqGain] using mul_le_mul_of_nonneg_left hg.2.2.2.2.2 hnonneg,
    rfl, hg.2.1, hg.2.2.2.1⟩

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
