/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoiseConsumers
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

def Lemma20ProbabilityBound : Prop :=
  ∀ (N : ℕ) [NeZero N] (s M P : ℕ) (G : Finset (ZMod N)) (y : ZMod N),
    2 ≤ M → 0 < P → s + (M - 1) * P < N → 2 * (M + G.card) ≤ N →
    Disjoint G ((Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))) →
    y ≠ 0 → (P : ZMod N) * y = 0 →
    let T := M + G.card
    let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))
    ∀ k : ℕ,
      let w := conditionalAmplifiedQFTCircuit N k
      let F : ℂ := (∑ r ∈ Finset.range M, ZMod.stdAddChar ((s + r * P : ZMod N) * y)) +
        (∑ z ∈ G, ZMod.stdAddChar (z * y))
      BornProb (Run (preparedMark (A ∪ G)) w (Ket 0)) y =
        (conditionalAmplifiedGain k (aqAngle N T)) ^ 2 / (N : ℝ) ^ 2 * ‖F‖ ^ 2 ∧
      BornProb (Run (preparedMark (A ∪ G)) w (Ket 0)) y ≤
        (conditionalAmplifiedGain k (aqAngle N T)) ^ 2 * (T : ℝ) ^ 2 / (N : ℝ) ^ 2

end Qatlib.Concepts.AmpTransform.ErrorStream
