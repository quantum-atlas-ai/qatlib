/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.SuccessRatio

def SuccessRatioAndRuntime : Prop :=
  (  ∀ (N : ℕ) (hN : 0 < N) (s M P : ℕ) (f : Fin N → Bool),
    2 ≤ M → 0 < P → s + (M - 1) * P < N → 2 * M ≤ N → AQMarkPromise f s M P →
    let S_ALG : Finset (Fin N) := Finset.univ.filter (fun y => y.val ≠ 0)
    MeasureProb (aqState N hN M (aqProgressionSet N s M P)) S_ALG =
      aqRatio N M * MeasureProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) S_ALG ∧
    (N : ℝ) ^ 2 / (4 * (M : ℝ) * ((N - M : ℕ) : ℝ)) * (1 - 2 * (M : ℝ) / (N : ℝ)) ^ 2 ≤
      aqRatio N M ∧
    aqRatio N M ≤ (N : ℝ) ^ 2 / (4 * (M : ℝ) * ((N - M : ℕ) : ℝ))) ∧
    (∀ (N : ℕ) (hN : 0 < N) (s M P B R : ℕ) (f : Fin N → Bool),
    2 ≤ M → 2 ≤ P → s + (M - 1) * P < N →
    2 * M ≤ N → M * P ≤ N → P ≤ B → 2 * B ^ 2 < N → AQMarkPromise f s M P →
    (∑ ω : Fin R → Fin N, aqFreshMass N hN M s P ω *
      ((aqRetry f s M B (aqRounds N M) (List.ofFn ω)).2 : ℝ)) ≤
        ((aqRounds N M + 3 : ℕ) : ℝ) / aqSuccessLower N M P)

end Qatlib.Concepts.AmpTransform.SuccessRatio
