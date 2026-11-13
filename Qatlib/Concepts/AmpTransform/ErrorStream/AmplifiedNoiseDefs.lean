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

/-!
# Specifications for amplified Fourier noise

This module defines three conjunctions that organize the expectation, density-boundary, and
continued-fraction results used for amplified Fourier noise. They collect named propositions
together with explicit reciprocal inequalities and recovery-window conditions in the setting of
[Cornwell2014].

The specifications retain both corrected boundary statements and negations of stronger original
formulations. In particular, the continued-fraction bundle requires exact denominator recovery
on the source successful window and containment of the good window when `P^2 ≤ N`.

## Main statements

* `stageAAmplifiedFourierNoiseClause23Spec`: the expectation and reciprocal-envelope
  specification.
* `stageAAmplifiedFourierNoiseClause24Spec`: the density, gain, and geometric-sum specification.
* `stageAAmplifiedFourierNoiseClause25Spec`: the boundary and continued-fraction recovery
  specification.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.LegendreWindow

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib.Concepts.AmpTransform.FullLayerCF Qatlib.Concepts.AmpTransform.LegendreWindow
open scoped Classical BigOperators ENNReal

/-- The conjunction of the minimized-error statement, corrected expected-noise envelope bridge,
negation of its original formulation, and strict reciprocal comparisons on `0 ≤ L < N - 1`
for `N > 1`. -/
def stageAAmplifiedFourierNoiseClause23Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinL) ∧
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridge) ∧
  (¬ Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeOriginal) ∧
  (∀ N : ℕ, 1 < N →
    (∀ L₁ L₂ : ℝ, 0 ≤ L₁ → L₁ < L₂ → L₂ < (N : ℝ) - 1 →
      1 / ((N : ℝ) - L₁ - 1) < 1 / ((N : ℝ) - L₂ - 1)) ∧
    (∀ L : ℝ, 0 ≤ L → L < (N : ℝ) - 1 →
      (1 / (N : ℝ)) < 1 / ((N : ℝ) - L - 1)))

/-- The conjunction of the dense zero-mode boundary, top-level all-marked gain, tangent-density
prefactor inequality, and error-stream geometric-sum statements. -/
def stageAAmplifiedFourierNoiseClause24Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.DenseZeroModeBoundary) ∧
  (Qatlib.Concepts.AmpTransform.ErrorStream.TopLevelAllMarkedGain) ∧
  (Qatlib.Concepts.AmpTransform.NoiseEnvelope.TanDensityPrefactorInequality) ∧
  (Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamGeometricSumZero)

/-- The conjunction of corrected and refuted Legendre boundary formulations, refutation of the
unrestricted non-strict convergent criterion, and exact denominator recovery for `P ≥ 2` on
the source successful window. It also requires inclusion of `aqGoodWindow` in that window
when `P^2 ≤ N` and `N, P` are positive. -/
def stageAAmplifiedFourierNoiseClause25Spec : Prop :=
  (Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundary) ∧
  (¬ Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryOriginal) ∧
  (¬ ∀ (ξ : ℝ) (q : ℚ), |ξ - q| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n : ℕ, q = ξ.convergent n) ∧
  (∀ (N P : ℕ) (_hP : 2 ≤ P) (y : Fin N) (_hy : y ∈
      Qatlib.Concepts.AmpTransform.FullLayerCF.aqSourceSuccessfulWindow N P),
    ∃ a n : ℕ, a < P ∧ Nat.Coprime a P ∧
      (a : ℚ) / P = ((y.val : ℝ) / N).convergent n ∧
      (((y.val : ℝ) / N).convergent n).den = P) ∧
  (∀ (N P : ℕ) (_hN : 0 < N) (_hP : 0 < P) (_hsize : P ^ 2 ≤ N),
    Qatlib.Concepts.AmpTransform.ErrorStream.aqGoodWindow N P ⊆
      Qatlib.Concepts.AmpTransform.FullLayerCF.aqSourceSuccessfulWindow N P)

end Qatlib.Concepts.AmpTransform.ErrorStream
