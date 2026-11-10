/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

def ErrorStreamSuccessRatios : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M L P : ℕ) (G : Finset (Fin N)) (h : Fin N → Bool)
    (E : Finset (Fin N)),
    2 ≤ M → 0 < P → s + (M - 1) * P < N → 2 * (M + L) ≤ N →
    G.card = L → Disjoint G (aqProgressionSet N s M P) →
    (∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) →
    (⟨0, hN⟩ : Fin N) ∉ E →
    let C := aqProgressionSet N s M P ∪ G
    let T := M + L
    MeasureProb (aqState N hN T C) E =
      aqRatio N T * MeasureProb (aqPhaseBaseline N hN C) E ∧
    MeasureProb (aqState N hN T C) E =
      2 * aqRatio N T * MeasureProb (aqQHSBaseline N hN h) (E ×ˢ Finset.univ) ∧
    (N : ℝ) ^ 2 / (4 * (T : ℝ) * ((N - T : ℕ) : ℝ)) *
        (1 - 2 * (T : ℝ) / (N : ℝ)) ^ 2 ≤ aqRatio N T ∧
    aqRatio N T ≤ (N : ℝ) ^ 2 / (4 * (T : ℝ) * ((N - T : ℕ) : ℝ))
end Qatlib.Concepts.AmpTransform.ErrorStream
