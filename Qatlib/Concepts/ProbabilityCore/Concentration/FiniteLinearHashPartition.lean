/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.FiniteLinearHash
import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashPartition
set_option warningAsError false

namespace Qatlib.Concepts.ProbabilityCore.Concentration

theorem finite_linear_hash_partition_deviation_bound
    (K I J X T : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype X] [Fintype T] [DecidableEq T]
    (embed : X → I → K) (side : X → T) (p : X → ℂ)
    (hinj : Function.Injective embed) :
    finiteHashAverage (weightedHashPartitionDeviation
      (fun M : Matrix I J K => fun x : X => finiteLinearMatrixHash M (embed x))
      side p) ≤
      Real.sqrt ((Fintype.card T : ℝ) *
        ((Fintype.card (J → K) : ℝ) - 1) * ∑ x : X, Complex.normSq (p x)) := by
  apply weighted_hash_partition_deviation_bound (Matrix I J K) X (J → K) T
  intro x y hxy
  exact finite_linear_matrix_hash_collision K I J (embed x) (embed y)
    (fun h => hxy (hinj h))

end Qatlib.Concepts.ProbabilityCore.Concentration
