/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.FullLayerCF.FullLayerCFDenoiseUniquePAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinLAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeAmpl
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.DenseZeroModeBoundaryAmpl
import Qatlib.Concepts.AmpTransform.ErrorStream.TopLevelAllMarkedGainAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.TanDensityPrefactorInequalityAmpl
import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamGeometricSumZeroAmpl
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.LegendreWindow

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib.Concepts.AmpTransform.FullLayerCF Qatlib.Concepts.AmpTransform.LegendreWindow
open scoped Classical BigOperators ENNReal

def stageAAmplifiedFourierNoiseClause23Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinL) ∧
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridge) ∧
  (¬ Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeOriginal) ∧
  (∀ N : ℕ, 1 < N →
    (∀ L₁ L₂ : ℝ, 0 ≤ L₁ → L₁ < L₂ → L₂ < (N : ℝ) - 1 →
      1 / ((N : ℝ) - L₁ - 1) < 1 / ((N : ℝ) - L₂ - 1)) ∧
    (∀ L : ℝ, 0 ≤ L → L < (N : ℝ) - 1 →
      (1 / (N : ℝ)) < 1 / ((N : ℝ) - L - 1)))

def stageAAmplifiedFourierNoiseClause24Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.DenseZeroModeBoundary) ∧
  (Qatlib.Concepts.AmpTransform.ErrorStream.TopLevelAllMarkedGain) ∧
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.TanDensityPrefactorInequality) ∧
  (Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamGeometricSumZero)

def stageAAmplifiedFourierNoiseClause25Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundary) ∧
  (¬ Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryOriginal) ∧
  (¬ ∀ (ξ : ℝ) (q : ℚ), |ξ - q| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n : ℕ, q = ξ.convergent n) ∧
  (∀ (N P : ℕ) (hP : 2 ≤ P) (y : Fin N) (hy : y ∈
      Qatlib.Concepts.AmpTransform.FullLayerCF.aqSourceSuccessfulWindow N P),
    ∃ a n : ℕ, a < P ∧ Nat.Coprime a P ∧
      (a : ℚ) / P = ((y.val : ℝ) / N).convergent n ∧
      (((y.val : ℝ) / N).convergent n).den = P) ∧
  (∀ (N P : ℕ) (hN : 0 < N) (hP : 0 < P) (hsize : P ^ 2 ≤ N),
    Qatlib.Concepts.AmpTransform.ErrorStream.aqGoodWindow N P ⊆
      Qatlib.Concepts.AmpTransform.FullLayerCF.aqSourceSuccessfulWindow N P)

end Qatlib.Concepts.AmpTransform.ErrorStream
