/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

def Proposition412ProductSliceTransfer : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ S : ℝ → ℕ → ℝ,
    (∀ v : ℝ, 0 < v → v ≤ 1 / 4 → ∀ d : ℕ, S v d ∈ Set.Icc 0 1) →
      (AAWith (muFamily p) S → AAWith (nuFamily p) (sliceTransferS S)) ∧
      (AAWith (nuFamily p) S → AAWith (muFamily p) (sliceTransferS S))

end Qatlib.Concepts.ProbabilityCore.DistributionAA
