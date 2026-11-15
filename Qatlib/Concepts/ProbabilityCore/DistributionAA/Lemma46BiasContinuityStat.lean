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

def Lemma46BiasContinuity : Prop :=
  ∀ n d : ℕ, ∀ f : (Fin n → Bool) → ℝ, (∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) →
    CubeDegreeLE d f →
    ∀ q r : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ r → r ≤ 1 →
      |cubeVar n (muWeight q n) f - cubeVar n (muWeight r n) f|
        ≤ 16 * (d : ℝ) ^ 2 * |q - r| ∧
      ∀ i : Fin n,
        |cubeInf n (muWeight q n) f i - cubeInf n (muWeight r n) f i|
          ≤ 16 * (d : ℝ) ^ 2 * |q - r|

end Qatlib.Concepts.ProbabilityCore.DistributionAA
