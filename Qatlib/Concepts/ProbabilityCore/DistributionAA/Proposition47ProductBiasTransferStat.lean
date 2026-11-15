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

def Proposition47ProductBiasTransfer : Prop :=
  ∀ p q : ℝ, 0 < p → p < 1 → 0 < q → q < 1 →
    ∀ S : ℝ → ℕ → ℝ, AAWith (muFamily p) S → ∀ D : ℕ, 0 < D →
      AAWith (muFamily q)
        (biasTransferS S (min (min p (1 - p)) (min q (1 - q))) D)

end Qatlib.Concepts.ProbabilityCore.DistributionAA
