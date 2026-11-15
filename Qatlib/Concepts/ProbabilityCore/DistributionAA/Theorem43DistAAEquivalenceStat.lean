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

def Theorem43DistributionalAAEquivalence : Prop :=
  ∀ p q : ℝ, 0 < p → p < 1 → 0 < q → q < 1 →
    (AAHolds (muFamily p) ↔ AAHolds (nuFamily q))

end Qatlib.Concepts.ProbabilityCore.DistributionAA
