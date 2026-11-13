/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.CostModels.Runtime
import Qatlib.Papers.QuantumSVM13.MinusReadout

/-!
# Quantum SVM cost-model identities

Combines the scalar runtime, accumulated-error, and readout-variance estimates for the quantum
SVM cost model. The dependence on dataset sizes appears through `Real.log (M * N)`, with
explicit inverse powers of the spectral cutoff and precision. See [RebentrostMohseniLloyd2014].

## Main statements

* `modeledQuantumSVM_main`: packages the runtime identity, error bound, and variance estimate.
* `modeledQuantumSVM_logarithmic`: factors out the logarithmic size dependence.

## References

* [Rebentrost et al., 2014][RebentrostMohseniLloyd2014]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QuantumSVM13.CostModels
open Qatlib.Papers.QuantumSVM13.MinusReadout

/-- For positive cutoff and precision, combines the modeled runtime identity with the
accumulated-error bound and the uniform readout-variance estimate
[RebentrostMohseniLloyd2014]. -/
theorem modeledQuantumSVM_main (εK ε M N : ℝ) (hεK : 0 < εK) (hε : 0 < ε) :
    modeledRepeatedRunTime (modeledEffectiveConditionNumber εK) ε M N
        = Real.log (M * N) * (1 / εK) ^ 3 * (1 / ε) ^ 3 ∧
      modeledStepAccumulatedError (1 / (εK * ε)) (modeledStepCount (1 / (εK * ε)) ε) ≤ ε ∧
      (∀ P : ℝ, 0 ≤ P → P ≤ 1 → P * (1 - P) / ε ^ 2 ≤ 1 / (4 * ε ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold modeledRepeatedRunTime modeledEffectiveConditionNumber
    field_simp
  · exact le_of_eq
      (modeledStepCount_achieves_epsilon (1 / (εK * ε)) ε (by positivity) (ne_of_gt hε))
  · intro P hP0 hP1
    exact swapTest_repetitions P ε hP0 hP1 hε

/-- For positive cutoff `εK` and precision `ε`, the repeated runtime model equals `Real.log (M *
N) * ((1 / εK) ^ 3 * (1 / ε) ^ 3)` [RebentrostMohseniLloyd2014]. -/
theorem modeledQuantumSVM_logarithmic (εK ε M N : ℝ) (hεK : 0 < εK) (hε : 0 < ε) :
    modeledRepeatedRunTime (modeledEffectiveConditionNumber εK) ε M N
      = Real.log (M * N) * ((1 / εK) ^ 3 * (1 / ε) ^ 3) := by
  rw [(modeledQuantumSVM_main εK ε M N hεK hε).1]
  ring

end Qatlib.Papers.QuantumSVM13.CostModels
