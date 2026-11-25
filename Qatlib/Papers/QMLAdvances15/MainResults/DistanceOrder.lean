/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMLAdvances15.MainResults.ProbDistance.SourceLemma1

@[expose] public section

/-!
# Comparing the distances from two projections

The Appendix B classifier compares distances inferred from two projection
probabilities. Each probability is weighted by its own normalization.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMLAdvances15.MainResults

open Qatlib.Papers.QMLAdvances15.MainResults

/-- Comparing the two normalization-weighted probabilities is equivalent to comparing distances. -/
theorem distance_lt {n : ℕ} {u vA vB : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) (hvA : vA ≠ 0) (hvB : vB ≠ 0)
    (pA pB : ℝ) (hpA : pA = ‖projectedData u vA‖ ^ 2) (hpB : pB = ‖projectedData u vB‖ ^ 2) :
    pA * (‖u‖ ^ 2 + ‖vA‖ ^ 2) < pB * (‖u‖ ^ 2 + ‖vB‖ ^ 2) ↔
      ‖u - vA‖ < ‖u - vB‖ := by
  have hweight {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
      ‖projectedData u v‖ ^ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) = ‖u - v‖ ^ 2 / 2 := by
    rw [projectedData_norm_sq hu hv]
    have hu0 := norm_pos_iff.mpr hu
    have hZ : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by positivity
    field_simp [hZ.ne']
  rw [hpA, hpB, hweight hvA, hweight hvB, div_lt_div_iff_of_pos_right (by norm_num)]
  exact sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)

end Qatlib.Papers.QMLAdvances15.MainResults
