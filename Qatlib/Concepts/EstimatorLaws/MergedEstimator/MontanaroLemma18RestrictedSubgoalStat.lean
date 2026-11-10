/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.MergedEstimator.Lemma18TransportContracts
import Qatlib.Concepts.AmplitudeSearch.NativeMean
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeSearch.NativeMean
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.NativeNumerics.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.MergedEstimator

open Qatlib

def MontanaroLemma18RestrictedSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A₁ A₂ : Matrix I I ℂ) (j : I)
    (f : I → ℚ) (σ : ℚ) (k r : ℕ) (γ : ℝ),
    ∀ (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ),
    4 ≤ k → 0 < σ → 0 ≤ γ → payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ →
    let μ₂ := ∑ i, BornProb (ApplyGate A₂ (Ket j)) i * (f i : ℝ);
    (∑ i, BornProb (ApplyGate A₂ (Ket j)) i * ((f i : ℝ) - μ₂) ^ 2) ≤ (σ : ℝ) ^ 2 →
    let law₁ := nativeSignedLaw A₁ j f σ k hA₁
      (fun x l => nativeLayerPrepare_unitary A₁
        (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))
      (fun x l => nativeLayerPrepare_unitary A₁
        (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _));
    law₁.probEvent
      (fun ξ : Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k) =>
        9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k
          < |(nativeSignedOutputMedian f σ k r ξ : ℝ) - μ₂|)
      ≤ (143 / 144 : ℝ) ^ r + (2 * r + 1) * γ
        + (Real.pi ^ 2 / Real.sqrt 6) * ((2 * r + 1) * 2 * (k + 2)
          * (2 * layerRepetitions k + 1) * (layerGrid k : ℕ)) * Real.sqrt γ

end Qatlib.Concepts.EstimatorLaws.MergedEstimator
