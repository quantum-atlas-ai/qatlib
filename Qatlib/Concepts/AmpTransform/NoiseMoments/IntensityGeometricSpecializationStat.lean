/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.NoiseStatistics.NoiseIntensityConsumers
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

def IntensityGeometricSpecialization : Prop :=
  ∀ (N L M : ℕ) [NeZero N] (y : ZMod N), y ≠ 0 → 0 < M + L →
    let T : ℝ := ((M + L : ℕ) : ℝ)
    let mu0 : ℝ := (L : ℝ) / T ^ 2
    let muM : ℝ := ((M : ℝ) ^ 2 + (L : ℝ)) / T ^ 2
    let varUnres : ℝ :=
      ((L : ℝ) ^ 2 - (L : ℝ) + 2 * (M : ℝ) ^ 2 * (L : ℝ)) / T ^ 4
    (0 ≤ mu0 ∧ mu0 ≤ muM) ∧
    (2 * y ≠ 0 →
      let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i * y)
      let F := fun ω : Fin L → ZMod N =>
        ‖(0 : ℂ) + S ω‖ ^ 2 / T ^ 2
      let FM := fun ω : Fin L → ZMod N =>
        ‖((M : ℂ)) + S ω‖ ^ 2 / T ^ 2
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, F ω) = mu0 ∧
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, FM ω) = muM ∧
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, (F ω - mu0) ^ 2) ≤ varUnres ∧
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, (FM ω - muM) ^ 2) ≤ varUnres) ∧
    (∀ L' : ℕ, 0 < M + L' →
      ((L' : ℝ) / (((M + L' : ℕ) : ℝ) ^ 2)) ≤
        (1 : ℝ) / ((M : ℝ) * (L' : ℝ) + (L' : ℝ) ^ 2) *
          ((M : ℝ) ^ 2 + (L' : ℝ))) ∧
    Filter.Tendsto (fun L' : ℕ => (L' : ℝ) / (((M + L' : ℕ) : ℝ) ^ 2))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun L' : ℕ =>
        (((L' : ℝ) ^ 2 - (L' : ℝ) + 2 * (M : ℝ) ^ 2 * (L' : ℝ)) /
          (((M + L' : ℕ) : ℝ) ^ 4)))
      Filter.atTop (nhds 0)

end Qatlib.Concepts.AmpTransform.NoiseMoments
