/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.AlgorithmInterface
import Qatlib.Papers.SemidirectHSP07.MainResults.Group

/-!
# Arithmetic certificates for query and success bounds

This module expresses the complexity discussion of [CosmePortugal2007] through `inputSize` and
elementary arithmetic inequalities. A plan with at most `inputSize r p` stages and at most its
cube queries per stage has at most its fourth power queries, while the displayed positive-stage
success expression equals three quarters.

The final results package these numerical bounds as existential certificates and as an
`HSPAlgorithm` record. That record stores numerical fields, so these statements concern the
certificates themselves.

## Main statements

- `plan_queries_le_polynomial` and `plan_queries_is_poly` bound the total query expression.
- `plan_success_gt_half` proves the rational success expression exceeds one half.
* `algorithm_certificate` combines the bounds, and `certificate_algorithm_exists` stores them in
  `HSPAlgorithm`.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

/-- The numerical input-size parameter `(r + 2) * bitLength p` for the semidirect-product
bounds. -/
def inputSize (r p : ℕ) : ℕ := (r + 2) * bitLength p

/-- Rewrites `polyBound r p` as one hundred times the cube of `inputSize r p`. -/
theorem polyBound_eq (r p : ℕ) : polyBound r p = 100 * (inputSize r p) ^ 3 := by
  rw [polyBound, inputSize]

/-- The input-size parameter is strictly positive for all natural `r` and `p`. -/
theorem inputSize_pos (r p : ℕ) : 0 < inputSize r p := by
  unfold inputSize
  exact Nat.mul_pos (by omega) (by unfold bitLength; omega)

/-- If the number of stages is at most `inputSize r p` and the queries per stage are at most its
cube, their product is at most its fourth power [CosmePortugal2007]. -/
theorem plan_queries_le_polynomial (r p stages stageQ : ℕ)
    (hst : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    stages * stageQ ≤ (inputSize r p) ^ 4 := by
  calc stages * stageQ ≤ inputSize r p * (inputSize r p) ^ 3 :=
        Nat.mul_le_mul hst hq
    _ = (inputSize r p) ^ 4 := by ring

/-- Under the stated stage and per-stage bounds, the total query expression has a polynomial
upper bound in `inputSize r p`, witnessed by coefficient one and degree four
[CosmePortugal2007]. -/
theorem plan_queries_is_poly (r p stages stageQ : ℕ)
    (hst : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    ∃ C k : ℕ, stages * stageQ ≤ C * (inputSize r p) ^ k :=
  ⟨1, 4, by simpa using plan_queries_le_polynomial r p stages stageQ hst hq⟩

/-- For a positive number of stages, the rational expression `1 - stages * (1 / (4 * stages))`
exceeds one half [CosmePortugal2007]. -/
theorem plan_success_gt_half (stages : ℕ) (h : 0 < stages) :
    (1 / 2 : ℚ) < 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ))) := by
  have hsQ : (0 : ℚ) < (stages : ℚ) := by exact_mod_cast h
  have hq : (stages : ℚ) * (1 / (4 * (stages : ℚ))) = 1 / 4 := by
    field_simp
  rw [hq]
  norm_num

/-- For a positive stage count satisfying the stated size bounds, there exist a query count
bounded by the fourth power of `inputSize r p` and a rational success value greater than one
half [CosmePortugal2007]. -/
theorem algorithm_certificate (r p stages stageQ : ℕ) (hst : 0 < stages)
    (hstle : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3) :
    ∃ (Q : ℕ) (s : ℚ), Q ≤ (inputSize r p) ^ 4 ∧ (1 / 2 : ℚ) < s :=
  ⟨stages * stageQ, 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ))),
    plan_queries_le_polynomial r p stages stageQ hstle hq,
    plan_success_gt_half stages hst⟩

/-- Packages the stage-count arithmetic certificate in an `HSPAlgorithm (SDG p r φ)` record
whose query field is at most `inputSize r p ^ 4` and whose success field exceeds one half.
The conclusion concerns the two numerical fields of that record [CosmePortugal2007]. -/
theorem certificate_algorithm_exists (r p stages stageQ : ℕ) (hst : 0 < stages)
    (hstle : stages ≤ inputSize r p) (hq : stageQ ≤ (inputSize r p) ^ 3)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    ∃ A : HSPAlgorithm (SDG p r φ),
      A.queryCount ≤ (inputSize r p) ^ 4 ∧ (1 / 2 : ℚ) < A.successProb := by
  refine ⟨⟨stages * stageQ, 1 - (stages : ℚ) * (1 / (4 * (stages : ℚ)))⟩,
    plan_queries_le_polynomial r p stages stageQ hstle hq,
    plan_success_gt_half stages hst⟩

end Qatlib.Papers.SemidirectHSP07.MainResults
