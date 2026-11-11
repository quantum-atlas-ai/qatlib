/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseDefs

/-!
# Amplified Fourier noise and boundary results

This module establishes the three bundled specifications for amplified Fourier noise defined in
`AmplifiedNoiseDefs`. The bundles collect expectation-envelope results, dense and all-marked
boundary statements, geometric-sum identities, and continued-fraction recovery guarantees in the
setting of [Cornwell2014].

The continued-fraction bundle includes a counterexample to a universal non-strict approximation
criterion: the rational number one lies at the allowed error boundary from one half but is never
one of its convergents.

## Main statements

* `stageA_amplified_fourier_noise_clause23`: establish the expectation and reciprocal-envelope
  bundle.
* `stageA_amplified_fourier_noise_clause24`: establish the density, gain, and geometric-sum
  bundle.
* `legendre_den_one_refuted`: refute the unrestricted non-strict convergent criterion.
* `stageA_amplified_fourier_noise_clause25`: establish the boundary and recovery-window bundle.

## References

* [Cornwell, 2014][Cornwell2014]
-/

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

/-- Establish `stageAAmplifiedFourierNoiseClause23Spec`, combining the minimized-error
statement, corrected noise-envelope bridge, refutation of its original version, and strict
reciprocal-envelope comparisons. -/
theorem stageA_amplified_fourier_noise_clause23 : stageAAmplifiedFourierNoiseClause23Spec :=
  ⟨errorExpectationMinimizedAtMinL, expectedNoiseEnvelopeBridge_answer,
    expectedNoiseEnvelopeBridge_false,
    fun N hN => ⟨fun L₁ L₂ _hL₁ h₁₂ h₂₃ => by
        have hB : 0 < (N : ℝ) - L₂ - 1 := by linarith
        have hlt : (N : ℝ) - L₂ - 1 < (N : ℝ) - L₁ - 1 := by linarith
        exact one_div_lt_one_div_of_lt hB hlt,
      fun L _hL hL₂ => by
        have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        have hB : 0 < (N : ℝ) - L - 1 := by linarith
        have hlt : (N : ℝ) - L - 1 < (N : ℝ) := by linarith
        exact one_div_lt_one_div_of_lt hB hlt⟩⟩

/-- Establish `stageAAmplifiedFourierNoiseClause24Spec`, combining the dense zero-mode boundary,
all-marked gain, tangent-density prefactor inequality, and error-stream geometric-sum
statements. -/
theorem stageA_amplified_fourier_noise_clause24 : stageAAmplifiedFourierNoiseClause24Spec :=
  ⟨denseZeroModeBoundary_answer, topLevelAllMarkedGain_answer,
    tanDensityPrefactorInequality_answer, errorStreamGeometricSumZero⟩

/-- No continued-fraction convergent of the real number one half equals the rational number one. -/
private theorem half_convergent_ne_one (n : ℕ) :
    (1 / 2 : ℝ).convergent n ≠ (1 : ℚ) := by
  match n with
  | 0 => rw [Real.convergent_zero]; norm_num
  | m + 1 =>
    rw [Real.convergent_succ]
    have hf : (Int.fract (1 / 2 : ℝ))⁻¹ = (2 : ℝ) := by norm_num [Int.fract]
    rw [hf]
    have h2 : ((2 : ℝ).convergent m) = 2 := Real.convergent_of_int (ξ := 2) m
    rw [h2]
    norm_num

/-- The universal claim that error at most `1 / (2 * q.den^2)` forces a rational `q` to be a
continued-fraction convergent is false, with `ξ = 1/2` and `q = 1` as a counterexample. -/
theorem legendre_den_one_refuted :
    ¬ ∀ (ξ : ℝ) (q : ℚ), |ξ - q| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n : ℕ, q = ξ.convergent n := by
  intro h
  have hw : |(1 / 2 : ℝ) - (1 : ℚ)| ≤ 1 / (2 * ((1 : ℚ).den : ℝ) ^ 2) := by norm_num
  obtain ⟨n, hn⟩ := h (1 / 2 : ℝ) 1 hw
  exact half_convergent_ne_one n hn.symm

/-- Establish `stageAAmplifiedFourierNoiseClause25Spec`, combining corrected Legendre boundary
results, refutations of the original and unrestricted non-strict criteria, and the stated
continued-fraction recovery-window guarantees. -/
theorem stageA_amplified_fourier_noise_clause25 : stageAAmplifiedFourierNoiseClause25Spec :=
  ⟨legendreFullBoundary_answer, legendreFullBoundary_false, legendre_den_one_refuted,
    fun N P hP y hy => aqSourceSuccessfulWindow_cf N P hP y hy,
    fun N P hN hP hsize => aqGoodWindow_subset_source N P hN hP hsize⟩

end Qatlib.Concepts.AmpTransform.ErrorStream
