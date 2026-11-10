/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
open scoped Classical

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Qatlib

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
