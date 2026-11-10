/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def AbelianStabilizerGenerationSubgoal : Prop :=
  ∀ (n k : ℕ), 0 < n → 0 < k →
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G), Fintype.card ↥H ≤ 2 ^ n →
    ∀ μ : FinDist G,
      (∀ L : Finset ↥H,
          |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)|
            ≤ 1 / ((6 : ℝ) * ↑k * ↑(n + 4))) →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
