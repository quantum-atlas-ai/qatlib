module

import Qatlib.Papers.StateConvLee10.StateConvert.EuclideanOutput

open scoped InnerProductSpace

namespace QatlibTests.StateConvLee10EuclideanOutput

/-- The clean target in two dimensions is the first Euclidean basis vector. -/
noncomputable def cleanTarget : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1

/-- A concrete output with a genuine nonzero Euclidean readout error of `1 / 100`. -/
noncomputable def cleanOutput : EuclideanSpace ℂ (Fin 2) :=
  cleanTarget + EuclideanSpace.single 1 ((1 / 100 : ℝ) : ℂ)

/-- The concrete target is normalized in the complex Euclidean norm. -/
theorem cleanTarget_norm : ‖cleanTarget‖ = 1 := by
  have hsq : ‖cleanTarget‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [cleanTarget]
  have hnonneg : 0 ≤ ‖cleanTarget‖ := norm_nonneg _
  have hsqrt : ‖cleanTarget‖ = Real.sqrt (‖cleanTarget‖ ^ 2) :=
    (Real.sqrt_sq hnonneg).symm
  rw [hsqrt, hsq, Real.sqrt_one]

/-- The output differs from the target by exactly one one-hundredth in Euclidean norm. -/
theorem cleanOutput_error_norm : ‖cleanOutput - cleanTarget‖ = 1 / 100 := by
  have hsq : ‖cleanOutput - cleanTarget‖ ^ 2 = (1 / 100 : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [cleanOutput, cleanTarget]
  have hnonneg : 0 ≤ ‖cleanOutput - cleanTarget‖ := norm_nonneg _
  have hsqrt : ‖cleanOutput - cleanTarget‖ =
      Real.sqrt (‖cleanOutput - cleanTarget‖ ^ 2) := (Real.sqrt_sq hnonneg).symm
  rw [hsqrt, hsq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 100)]

/-- The Dev-layer error-to-overlap theorem gives a concrete `99 / 100` clean overlap bound on a
non-degenerate two-dimensional register. -/
theorem cleanOutput_overlap_consumer :
    99 / 100 ≤ (inner ℂ cleanOutput cleanTarget).re ∧ ‖cleanOutput‖ ≤ 101 / 100 := by
  obtain ⟨C, hCpos, hCle, hCge, hmain⟩ :=
    Qatlib.Papers.StateConvLee10.StateConvert.source_euclidean_error_to_clean_overlap
  have hmain' := hmain 2 (by norm_num) cleanOutput cleanTarget (1 / 100)
    (by norm_num) cleanTarget_norm (by
      rw [cleanOutput_error_norm]
      simpa using
        mul_le_mul_of_nonneg_right hCge (by norm_num : (0 : ℝ) ≤ 1 / 100))
  have hle : C * (1 / 100 : ℝ) ≤ 1 / 100 := by
    calc C * (1 / 100 : ℝ) ≤ 1 * (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hCle (by norm_num : (0 : ℝ) ≤ 1 / 100)
      _ = 1 / 100 := by ring
  constructor
  · exact le_trans (by linarith) hmain'.1
  · exact le_trans hmain'.2 (by
      have hsum : 1 + C * (1 / 100 : ℝ) ≤ 101 / 100 := by linarith
      exact hsum)

end QatlibTests.StateConvLee10EuclideanOutput
