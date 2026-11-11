/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Near-uniform generation specification

`NearUniformGenerationSubgoal` specifies a generation bound for independent samples whose subset
masses approximate the uniform law of a target subgroup. It includes a finite proper-subgroup
covering family and separates the contribution from samples outside the target from the
contribution of containment in proper subgroups. For background, see [Kitaev1995].

## Main statements

* `NearUniformGenerationSubgoal`: states the subgroup-cover properties and generation failure
  estimate.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

/-- The proposition that for any law approximating uniform subgroup subset masses within
nonnegative δ, there is a proper-subgroup covering family of size below the subgroup order
and the generation failure probability is at most `l*δ + maxs.card*(1/2+δ)^l`. -/
def NearUniformGenerationSubgoal : Prop :=
  ∀ (l : ℕ) (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (μ : FinDist G) (δ : ℝ), 0 ≤ δ →
    (∀ L : Finset ↥H,
        |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ) →
    ∃ maxs : Finset (AddSubgroup ↥H),
      (∀ L ∈ maxs, L < ⊤) ∧
      (∀ K : AddSubgroup ↥H, K < ⊤ → ∃ L ∈ maxs, K ≤ L) ∧
      maxs.card < Fintype.card ↥H ∧
      FinDist.probEvent (L := l) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ (l : ℝ) * δ + (maxs.card : ℝ) * (1 / 2 + δ) ^ l

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
