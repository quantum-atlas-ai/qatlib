/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.Theorem8RelativeContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

def MontanaroTheorem6RelativeTrialSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (B ε : ℝ) (N k : ℕ),
    ∀ (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i),
    1 ≤ B → 0 < ε → ε ≤ 1 → 32 * B ≤ (N : ℝ) → 4 ≤ k →
    3 * Real.sqrt (B + 1) * (1 / 2 : ℝ) ^ k ≤ ε →
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i;
    0 < μ → (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i - μ) ^ 2) ≤ B * μ ^ 2 →
    (theorem6TrialLaw A j f B N k hA hf).probEvent
      (fun ξ : Fin 1 → ((Fin N → I) × LayerRecord k) =>
        ε * μ < |theorem6Output f B N k (ξ 0) - μ|)
      ≤ 1 / 4

end Qatlib.Concepts.EstimatorLaws.TvStability
