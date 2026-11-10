/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedExpectedDistance
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMetadataHybrid
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Matrix.Norms.L2Operator

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
