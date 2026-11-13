/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.ErrorMetrics.CoherenceCounterexample

/-!
# Cauchy mixtures and coherent output probabilities

This module compares coherent evolution with a classical Cauchy mixture of spectral-unitary
outcome probabilities in the Koopman simulation setting of [ZhangEtAl2026]. For the fixed decay
example, `cauchy_mixture_born_zero` evaluates the Cauchy-weighted probability of the `false`
outcome to exactly `1 / 2`.

The result `coherent_ne_cauchy_born_mixture` shows that the corresponding probability of the
normalized coherent output differs from this mixture. The example distinguishes the probability
obtained after coherent state evolution from averaging the probabilities of individual unitary
evolutions.

## Main statements

- `cauchy_mixture_born_zero` computes the Cauchy mixture for the decay example.
* `coherent_ne_cauchy_born_mixture` proves a discrepancy between the normalized coherent output
  and that mixture.

## References

* [Zhang et al., 2026][ZhangEtAl2026], Quantum simulation of real-world nonlinear dynamics via
  Koopman method.
-/

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics.CauchyMixture

/-- For the fixed decay example, averaging the `false`-outcome Born probabilities of the
spectral-unitary outputs against the standard Cauchy density gives exactly `1 / 2`. -/
theorem cauchy_mixture_born_zero :
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) *
      BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) false)=1/2 := by
  simp_rw [spectral_born]
  rw [integral_mul_const, static_lchs_cauchy_density_integral]
  norm_num

/-- In the fixed decay example, the `false`-outcome probability of the normalized coherent
output differs from the Cauchy-weighted mixture of spectral-unitary outcome probabilities. -/
theorem coherent_ne_cauchy_born_mixture :
    BornProb (normalizedState decayOutput) false ≠
      (∫ k : ℝ, (1/(Real.pi*(1+k^2))) *
        BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) false) := by
  rw [coherent_born_zero, cauchy_mixture_born_zero]
  norm_num

end Qatlib.Papers.KoopmanSim26.ErrorMetrics.CauchyMixture
