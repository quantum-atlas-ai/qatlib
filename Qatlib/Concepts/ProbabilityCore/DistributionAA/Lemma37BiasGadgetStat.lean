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

def Lemma37BiasGadget : Prop :=
  ∀ p q : ℝ, 0 < p → p < 1 → 0 ≤ q → q ≤ 1 → ∀ m : ℕ,
    ∃ g : (Fin m → Bool) → Bool,
      q ≤ cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0) ∧
        cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)
          ≤ q + (2 : ℝ) ^ (-(min p (1 - p) * m))

end Qatlib.Concepts.ProbabilityCore.DistributionAA
