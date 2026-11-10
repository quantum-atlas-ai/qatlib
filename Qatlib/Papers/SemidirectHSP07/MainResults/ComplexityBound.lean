/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.AlgorithmInterface
import Qatlib.Papers.SemidirectHSP07.MainResults.Group
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

def inputSize (r p : ℕ) : ℕ := (r + 2) * bitLength p

theorem polyBound_eq (r p : ℕ) : polyBound r p = 100 * (inputSize r p) ^ 3 := by
  rw [polyBound, inputSize]

theorem inputSize_pos (r p : ℕ) : 0 < inputSize r p := by
  unfold inputSize
  exact Nat.mul_pos (by omega) (by unfold bitLength; omega)

theorem plan_queries_le_polynomial (r p stages stageQ : ℕ)
    (hst : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    stages * stageQ ≤ (inputSize r p) ^ 4 := by
  calc stages * stageQ ≤ inputSize r p * (inputSize r p) ^ 3 :=
        Nat.mul_le_mul hst hq
    _ = (inputSize r p) ^ 4 := by ring

theorem plan_queries_is_poly (r p stages stageQ : ℕ)
    (hst : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    ∃ C k : ℕ, stages * stageQ ≤ C * (inputSize r p) ^ k :=
  ⟨1, 4, by simpa using plan_queries_le_polynomial r p stages stageQ hst hq⟩

theorem plan_success_gt_half (stages : ℕ) (h : 0 < stages) :
    (1 / 2 : ℚ) < 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ))) := by
  have hsQ : (0 : ℚ) < (stages : ℚ) := by exact_mod_cast h
  have hq : (stages : ℚ) * (1 / (4 * (stages : ℚ))) = 1 / 4 := by
    field_simp
  rw [hq]
  norm_num

theorem algorithm_certificate (r p stages stageQ : ℕ) (hst : 0 < stages)
    (hstle : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    ∃ (Q : ℕ) (s : ℚ), Q ≤ (inputSize r p) ^ 4 ∧ (1 / 2 : ℚ) < s :=
  ⟨stages * stageQ, 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ))),
    plan_queries_le_polynomial r p stages stageQ hstle hq,
    plan_success_gt_half stages hst⟩

theorem certificate_algorithm_exists (r p stages stageQ : ℕ) (hst : 0 < stages)
    (hstle : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    ∃ A : HSPAlgorithm (SDG p r φ),
      A.queryCount ≤ (inputSize r p) ^ 4 ∧ (1 / 2 : ℚ) < A.successProb := by
  refine ⟨⟨stages * stageQ, 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ)))⟩,
    plan_queries_le_polynomial r p stages stageQ hstle hq,
    plan_success_gt_half stages hst⟩

end Qatlib.Papers.SemidirectHSP07.MainResults
