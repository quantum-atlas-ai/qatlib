/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.CostModels.MainResult
import Qatlib.Papers.QuantumSVM13.MinusReadout.SwapTest

/-!
# A finite scalar cost consumer (QuantumSVM13)

This module feeds finite natural dimensions and an exact finite swap-test branch
probability into the scalar models from `Runtime.lean`.  The resulting numbers
are a typed arithmetic instance of those models only: they do not construct an
SVM circuit, identify a physical run time, or provide a statistical confidence
statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Qatlib.Papers.QuantumSVM13.CostModels

open Qatlib.Papers.QuantumSVM13.CostModels

open Qatlib.Papers.QuantumSVM13.MinusReadout
open Qatlib.Papers.QuantumSVM13.MinusReadout


/-- The repeated-run scalar model at finite natural data dimensions. -/
noncomputable def modeledFiniteRunTime (εK ε : ℝ) (M N : ℕ) : ℝ :=
  modeledRepeatedRunTime (modeledEffectiveConditionNumber εK) ε (M : ℝ) (N : ℝ)

/-- The finite natural-dimension wrapper agrees with the scalar runtime model's
logarithmic form whenever both accuracy parameters are positive. -/
theorem modeledFiniteRunTime_eq (εK ε : ℝ) (M N : ℕ)
    (hεK : 0 < εK) (hε : 0 < ε) :
    modeledFiniteRunTime εK ε M N =
      Real.log ((M : ℝ) * (N : ℝ)) *
        ((1 / εK) ^ 3 * (1 / ε) ^ 3) := by
  unfold modeledFiniteRunTime
  simpa [mul_assoc] using
    modeledQuantumSVM_logarithmic εK ε (M : ℝ) (N : ℝ) hεK hε

/-- A finite-dimensional consumer of the scalar models: the runtime identity,
exact accumulated step error, and reciprocal-eigenvalue error bound all hold
under the explicitly supplied positive accuracy premises. -/
theorem modeledFiniteCost_profile (εK ε : ℝ) (M N : ℕ)
    (hεK : 0 < εK) (hε : 0 < ε) :
    modeledFiniteRunTime εK ε M N =
        Real.log ((M : ℝ) * (N : ℝ)) * (1 / εK) ^ 3 * (1 / ε) ^ 3 ∧
      modeledStepAccumulatedError
          (modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε)
          (modeledStepCount
            (modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε) ε) = ε ∧
      modeledRelativeEigenvalueError
          (modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε) εK ≤ ε := by
  have ht0 : modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε ≠ 0 := by
    unfold modeledTotalEvolutionTime modeledEffectiveConditionNumber
    positivity
  refine ⟨?_, ?_, ?_⟩
  · simpa [mul_assoc] using modeledFiniteRunTime_eq εK ε M N hεK hε
  · exact modeledStepCount_achieves_epsilon
      (modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε) ε ht0
      (ne_of_gt hε)
  · rw [modeledTotalEvolutionTime_eq]
    exact modeledRelativeEigenvalueError_le εK εK ε hεK hε le_rfl

/-- The exact finite two-state minus branch inherits the scalar swap-test
repetition budget for every positive accuracy.  This remains a conditional
scalar budget inequality, not a claim about an implemented sampling circuit. -/
theorem classical_basis_query_budget_le (ε : ℝ) (hε : 0 < ε) :
    minusBranchWeight classicalZero2 classicalOne2 *
        (1 - minusBranchWeight classicalZero2 classicalOne2) / ε ^ 2 ≤
      1 / (4 * ε ^ 2) := by
  rw [classical_basis_minusBranchWeight]
  exact swapTest_repetitions (1 / 2 : ℝ) ε (by norm_num) (by norm_num) hε

/-- At `εK = 1/2`, `ε = 1/4`, and two-by-two finite dimensions, the scalar
consumer yields total evolution time `8`, step count `256`, runtime
`512 log 4`, reciprocal-eigenvalue error at most `1/4`, and the concrete
finite minus-branch repetition budget `4`.  These are model values only. -/
theorem modeledQuantumSVM_two_by_two_consumer :
    modeledFiniteRunTime (1 / 2 : ℝ) (1 / 4 : ℝ) 2 2 = 512 * Real.log 4 ∧
      modeledStepAccumulatedError 8 256 = (1 / 4 : ℝ) ∧
      modeledRelativeEigenvalueError 8 (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ∧
      minusBranchWeight classicalZero2 classicalOne2 *
          (1 - minusBranchWeight classicalZero2 classicalOne2) / (1 / 4 : ℝ) ^ 2 =
        4 := by
  have hprofile := modeledFiniteCost_profile (1 / 2 : ℝ) (1 / 4 : ℝ) 2 2
    (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hprofile.1 using 1
    norm_num
    ring
  · convert hprofile.2.1 using 1
    norm_num [modeledTotalEvolutionTime, modeledEffectiveConditionNumber, modeledStepCount]
  · convert hprofile.2.2 using 1
    norm_num [modeledTotalEvolutionTime, modeledEffectiveConditionNumber]
  · rw [classical_basis_minusBranchWeight]
    norm_num

end Qatlib.Papers.QuantumSVM13.CostModels
