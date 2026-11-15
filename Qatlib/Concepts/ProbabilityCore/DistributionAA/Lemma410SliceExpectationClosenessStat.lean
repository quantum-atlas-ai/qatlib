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

def Lemma410ProductSliceExpectationCloseness : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ n d : ℕ, ∀ f : (Fin n → Bool) → ℝ,
    (∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) → CubeDegreeLE d f →
      |cubeExpect n (muWeight p n) f - cubeExpect n (nuWeight p n) f|
        ≤ 16 * (d : ℝ) ^ 2 / Real.sqrt (n : ℝ)

end Qatlib.Concepts.ProbabilityCore.DistributionAA
