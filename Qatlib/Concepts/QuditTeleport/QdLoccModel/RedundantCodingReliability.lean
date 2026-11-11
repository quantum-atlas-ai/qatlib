/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# A repeated-observation reliability contract

`RedundantCodingReliability` states that two finite probability laws with distinct expectations
of a binary statistic can be distinguished by repeated independent sampling. The test compares
the sample sum with the midpoint of the two expected sums and bounds both error probabilities.
The communication setting is teleportation [BennettEtAl1993Teleportation]; see also [Wilde2017]
for the information-theoretic background.

## Main statements

* `RedundantCodingReliability`: The proposition that a strict expectation gap for a binary
  statistic permits a positive sample size making both midpoint-threshold discrimination errors
  at most any prescribed positive `ε`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Wilde, 2017][Wilde2017]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
open scoped Classical

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Qatlib

/-- The proposition that a strict expectation gap for a binary statistic permits a positive
sample size making both midpoint-threshold discrimination errors at most any prescribed
positive `ε`. -/
def RedundantCodingReliability : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (qr qs : FinDist X) (A : X → ℝ),
    (∀ x, A x = 0 ∨ A x = 1) → 0 < qr.expect A - qs.expect A →
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, 0 < k ∧
        (∑ ω ∈ Finset.univ.filter
          (fun ω : Fin k → X => (∑ i, A (ω i)) < k * (qr.expect A + qs.expect A) / 2),
          (independentSampleLaw (fun _ : Fin k => qr)).prob ω) ≤ ε ∧
        (∑ ω ∈ Finset.univ.filter
          (fun ω : Fin k → X => k * (qr.expect A + qs.expect A) / 2 ≤ (∑ i, A (ω i))),
          (independentSampleLaw (fun _ : Fin k => qs)).prob ω) ≤ ε

end Qatlib.Concepts.QuditTeleport.QdLoccModel
