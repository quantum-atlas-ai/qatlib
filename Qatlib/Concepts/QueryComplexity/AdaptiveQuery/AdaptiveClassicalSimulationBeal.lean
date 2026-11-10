/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationStat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveBlockSensitivityQueryBoundBeal
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityDominanceCorollaryBeal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open scoped Classical BigOperators

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

theorem adaptiveClassicalSimulation : AdaptiveClassicalSimulation :=
  adaptiveClassicalSimulation_of_queryBound adaptiveBlockSensitivityQueryBound

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
