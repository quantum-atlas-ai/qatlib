/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

def DenseZeroModeBoundary : Prop :=
  (∀ (N : ℕ) (_hN : 0 < N) (T : ℕ), 2 * T ≤ N → 0 < T →
    let θ := aqAngle N T
    let k := aqRounds N T
    0 ≤ (Real.cos (2 * (k : ℝ) * θ)) ^ 2 ∧
    (Real.cos (2 * (k : ℝ) * θ)) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2) ∧
  (let θ := aqAngle 4 3
   let k := aqRounds 4 3
   (Real.sin θ) ^ 2 = (3 : ℝ) / 4 ∧
   (Real.cos (2 * (k : ℝ) * θ)) ^ 2 = 1 ∧
   (Real.sin (2 * θ)) ^ 2 = (3 : ℝ) / 4)

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
