/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationStat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveBlockSensitivityQueryBoundBeal
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityDominanceCorollaryBeal

/-!
# Classical simulation of adaptive quantum queries

This module proves `AdaptiveClassicalSimulation` from the adaptive block sensitivity query bound
and deterministic decision tree bounds. A well formed observed circuit of query depth `T`
computing a total Boolean function with error at most one third yields an exact deterministic
query tree of cost at most `4096T⁶`.

The result implements the polynomial relation between deterministic and bounded error quantum
query complexity developed in [BealsEtAl2001].

## Main statements

* `adaptiveClassicalSimulation_of_queryBound`: derives classical simulation from adaptive block
  sensitivity bounds.
* `adaptiveClassicalSimulation`: gives the exact deterministic tree and complexity bound.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open scoped Classical BigOperators

/-- The adaptive block sensitivity query bound implies an exact deterministic simulation with at
most `4096T⁶` queries for any well formed observed circuit of depth `T` computing with error
at most one third. -/
theorem adaptiveClassicalSimulation_of_queryBound
    (hquery : AdaptiveBlockSensitivityQueryBound) : AdaptiveClassicalSimulation := by
  intro n W _ _ _ P ψ f hP hψ herr
  have hbs := (hquery n W P ψ f hP hψ).1 herr
  have hC := lemma52CertificateBlockSensitivity n f
  have hcube : blockSensitivity f^3 ≤ 4096*observedQueryDepth P^6 := by
    calc
      _ ≤ (16*observedQueryDepth P^2)^3 := Nat.pow_le_pow_left hbs 3
      _ = _ := by ring
  obtain ⟨t,ht,hcost⟩ := certificateTree_exists f
  refine ⟨⟨t,ht,?_⟩,(sensitivityDominanceCorollary n f).trans hcube⟩
  calc
    t.MaxQueries ≤ oneCertificateComplexity f*blockSensitivity f := hcost
    _ ≤ blockSensitivity f^2*blockSensitivity f :=
      Nat.mul_le_mul_right _ (hC.1.trans hC.2)
    _ = blockSensitivity f^3 := by ring
    _ ≤ _ := hcube

/-- A total Boolean function computed by a well formed observed circuit of query depth `T` with
error at most one third has an exact deterministic query tree and deterministic query
complexity bounded by `4096T⁶`. This follows the polynomial method of [Beals et al., Theorem
5.4][BealsEtAl2001]. -/
theorem adaptiveClassicalSimulation : AdaptiveClassicalSimulation :=
  adaptiveClassicalSimulation_of_queryBound adaptiveBlockSensitivityQueryBound

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
