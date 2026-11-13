/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedExpectedDistance
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMetadataHybrid

/-!
# Expected query hybrid theorem

`observed_expected_oracle_hybrid` proves `PairedExpectedHybridSpecification` by combining the
paired state distance estimate with the bound for scores of classical branch metadata. It
provides an expected query version of the oracle hybrid method associated with
[BennettEtAl1997].

The resulting specification controls both terminal state distance and changes in any score
bounded in absolute value by one. If both expected query counts are at most `Q` and a score
separates the executions by at least twice a nonnegative `gamma`, it also bounds `gamma` squared
in terms of `Q` and the oracle difference.

## Main statements

* `observed_expected_oracle_hybrid` establishes the complete paired expected hybrid
  specification.
* Its proof combines `observed_paired_expected_distance` and
  `observed_metadata_score_sq_le_distance`.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Matrix.Norms.L2Operator

/-- Establishes the paired expected hybrid specification, including its terminal distance,
bounded metadata score, and common query budget conclusions. -/
theorem observed_expected_oracle_hybrid : PairedExpectedHybridSpecification := by
  intro I _ _ A B P ψ hA hB hP hψ
  let q := Real.sqrt
    (expectedObservedQueries A P ψ * expectedObservedQueries B P ψ)
  have hd := observed_paired_expected_distance A B P ψ hA hB hP hψ
  have hread (score : Bool → List (ℕ × ℕ) → ℝ)
      (hs : ∀ b record, |score b record| ≤ 1) :
      (observedMetadataScore A P ψ score - observedMetadataScore B P ψ score) ^ 2 ≤
        8 * ‖A - B‖ * q := by
    have h := observed_metadata_score_sq_le_distance A B P ψ hA hB hP hψ score hs
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4)
    dsimp only [q]
    nlinarith
  refine ⟨hd, hread, ?_⟩
  intro score γ Q hs hγ hEA hEB hgap
  have hQ : 0 ≤ Q := (expectedObservedQueries_nonneg A P ψ).trans hEA
  have hprod : expectedObservedQueries A P ψ * expectedObservedQueries B P ψ ≤ Q ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hEA hEB (expectedObservedQueries_nonneg B P ψ) hQ
  have hq : q ≤ Q := Real.sqrt_le_iff.mpr ⟨hQ, hprod⟩
  have hweighted := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ 8 * ‖A - B‖)
  have hgapsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * γ) hgap 2
  rw [sq_abs] at hgapsq
  have hscore := hread score hs
  nlinarith

end Qatlib.Concepts.AdversaryBounds.AdvDuality
