/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.MergedEstimator.Lemma18TransportContracts
import Qatlib.Concepts.AmplitudeSearch.NativeMean

/-!
# Restricted signed-estimator transport contract

States the restricted signed rational-estimator stability property associated with Lemma 18 of
[Montanaro2015]. Its hypotheses compare payoff-value laws of two unitary preparations and bound
the variance under the second preparation; the proposition itself supplies no proof.

## Main statements

* `MontanaroLemma18RestrictedSubgoal` specifies a median failure bound at error `9 * σ * 2⁻ᵏ`,
  with intrinsic failure `(143 / 144)^r` and explicit perturbation terms.

## References

* [Montanaro, 2015][Montanaro2015]
-/

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

/-- The proposition requiring the restricted Lemma 18 stability bound of [Montanaro2015] for the
native signed rational median estimator. It assumes `k ≥ 4`, positive `σ`, payoff-value L1
distance at most `2 * γ`, and variance at most `σ²` under the second preparation. -/
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
