/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Composite measurement near-uniformity specification

`CompositeMeasurementNearUniformSubgoal` states a finite mixture estimate for noisy
subgroup-label measurements. A uniform mixture of conditional laws that each recover their own
label with error at most δ must approximate uniform subgroup probabilities on every subset to
within δ. For background, see [Kitaev1995].

## Main statements

* `CompositeMeasurementNearUniformSubgoal`: specifies the subsetwise error bound for noisy
  composite measurement.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

/-- The proposition that a uniform mixture of subgroup-indexed output laws, each returning its
index with probability at least `1 - δ` for nonnegative δ, has subset masses within δ of the
uniform subgroup law. -/
def CompositeMeasurementNearUniformSubgoal : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (μ : FinDist G) (cond : ↥H → FinDist G) (δ : ℝ), 0 ≤ δ →
    (∀ g : G, μ.prob g =
      (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g) →
    (∀ h' : ↥H, 1 - δ ≤ (cond h').prob (h' : G)) →
    ∀ L : Finset ↥H,
      |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
