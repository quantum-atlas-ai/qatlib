/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

def CompositeMeasurementNearUniformSubgoal : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (μ : FinDist G) (cond : ↥H → FinDist G) (δ : ℝ), 0 ≤ δ →
    (∀ g : G, μ.prob g =
      (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g) →
    (∀ h' : ↥H, 1 - δ ≤ (cond h').prob (h' : G)) →
    ∀ L : Finset ↥H,
      |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
