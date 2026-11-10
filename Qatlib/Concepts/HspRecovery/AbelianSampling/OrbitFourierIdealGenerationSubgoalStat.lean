/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasis
set_option warningAsError false

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def OrbitFourierIdealGenerationSubgoal : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E],
      Fintype.card E ≤ 2 ^ n →
      (∀ χ : AddChar E ℂ, (fourierBornDist E).prob χ = (Fintype.card E : ℝ)⁻¹)
      ∧ Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) (fourierBornDist E)
          (fun hs => Subgroup.closure (Set.range hs) ≠ ⊤) ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
