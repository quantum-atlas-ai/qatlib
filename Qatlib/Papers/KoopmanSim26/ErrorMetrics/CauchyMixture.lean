/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.ErrorMetrics.CoherenceCounterexample
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.ErrorMetrics.Coherence

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics.CauchyMixture

theorem cauchy_mixture_born_zero :
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) *
      BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) false)=1/2 := by
  simp_rw [spectral_born]
  rw [integral_mul_const, static_lchs_cauchy_density_integral]
  norm_num

theorem coherent_ne_cauchy_born_mixture :
    BornProb (normalizedState decayOutput) false ≠
      (∫ k : ℝ, (1/(Real.pi*(1+k^2))) *
        BornProb (spectralUnitary decayL 0 1 k *ᵥ plusInput) false) := by
  rw [coherent_born_zero, cauchy_mixture_born_zero]
  norm_num

end Qatlib.Papers.KoopmanSim26.ErrorMetrics.CauchyMixture
