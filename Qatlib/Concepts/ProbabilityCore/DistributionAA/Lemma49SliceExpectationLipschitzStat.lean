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

def Lemma49SliceExpectationLipschitz : Prop :=
  ∀ n d : ℕ, ∀ f : (Fin n → Bool) → ℝ, (∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) →
    CubeDegreeLE d f →
    ∀ t u : ℕ, t ≤ n → u ≤ n →
      |cubeExpect n (sliceWeight n t) f - cubeExpect n (sliceWeight n u) f|
        ≤ (8 * (d : ℝ) ^ 2 / (n : ℝ)) * |(t : ℝ) - (u : ℝ)|

end Qatlib.Concepts.ProbabilityCore.DistributionAA
