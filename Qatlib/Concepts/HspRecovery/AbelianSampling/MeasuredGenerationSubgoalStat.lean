/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def AbelianStabilizerMeasuredGenerationSubgoal : Prop :=
  ∀ (n : ℕ), 0 < n →
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G), Fintype.card ↥H ≤ 2 ^ n →
    ∀ (μ : FinDist G) (cond : ↥H → FinDist G),
      (∀ g : G, μ.prob g =
        (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g) →
      (∀ h' : ↥H,
          1 - 1 / ((6 : ℝ) * ↑(n + 4)) ≤ (cond h').prob (h' : G)) →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
