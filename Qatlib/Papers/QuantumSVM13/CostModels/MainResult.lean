/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.CostModels.Runtime
import Qatlib.Papers.QuantumSVM13.MinusReadout
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QuantumSVM13.CostModels
open Qatlib.Papers.QuantumSVM13.MinusReadout

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

theorem modeledQuantumSVM_logarithmic (εK ε M N : ℝ) (hεK : 0 < εK) (hε : 0 < ε) :
    modeledRepeatedRunTime (modeledEffectiveConditionNumber εK) ε M N
      = Real.log (M * N) * ((1 / εK) ^ 3 * (1 / ε) ^ 3) := by
  rw [(modeledQuantumSVM_main εK ε M N hεK hε).1]
  ring

end Qatlib.Papers.QuantumSVM13.CostModels
