/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingProgram

/-!
# Specification of exact resampling performance

`ExactResamplingUpper` states a water-level existence and circuit-performance contract for
normalized rational tables with a strict tight bracket and positive target coordinates. It
records the exact clipped-fill output, prescribed squared overlap, circuit validity, and
separate counts for source queries, data queries, and fixed gates.

The specification concerns the upper-bound construction associated with quantum rejection
sampling [OzolsRoettelerRoland2013]; see [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.ExactResampling
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- The exact-resampling upper-bound contract for normalized rational tables with positive
target entries and a strict tight level bracket. It requires a level realizing any fidelity
between the endpoints, together with exact output, circuit-validity, overlap, and
query-count guarantees for every compatible source preparation. -/
def ExactResamplingUpper : Prop :=
  ∀ (m : ℕ) (π σ : Fin m → ℚ) (γlo γhi : ℝ),
    (∀ i, 0 ≤ π i) → (∀ i, 0 < σ i) →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    γlo < γhi →
    (∀ i, 0 < π i → γlo * (σ i : ℝ) ≤ (π i : ℝ)) →
    (∃ i₀, 0 < π i₀ ∧ γlo * (σ i₀ : ℝ) = (π i₀ : ℝ)) →
    (∀ i, (π i : ℝ) ≤ γhi * (σ i : ℝ)) →
    (∃ i₁, 0 < π i₁ ∧ (π i₁ : ℝ) = γhi * (σ i₁ : ℝ)) →
    ∀ p : ℝ, waterPmin π σ ≤ p → p ≤ waterPmax π σ →
      ∃ γ : ℝ, γlo ≤ γ ∧ γ ≤ γhi ∧ 0 < levelMass π σ γ ∧
        levelDot π σ γ ^ 2 = p * levelMass π σ γ ∧
        ∀ (D : ℕ) (ξ : Fin m → QState (Fin D))
          (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D),
          (∀ i, Normalized (ξ i)) → U ∈ Matrix.unitaryGroup _ ℂ →
          U *ᵥ Ket j₀ = waterSource π ξ →
          PreparedCircuitValid (resamplingExactWord π σ γ j₀) ∧
          resamplingExactOutput π σ γ U j₀ =
            ((1 / Real.sqrt (levelMass π σ γ) : ℝ) : ℂ) •
              resamplingFamily (levelFill π σ γ) ξ ∧
          Normalized (resamplingExactOutput π σ γ U j₀) ∧
          MeasureProb (resamplingExactOutput π σ γ U j₀) (waterEvent m D) = 0 ∧
          Complex.normSq (Inner (resamplingFamily (fun i => (σ i : ℝ)) ξ)
            (resamplingExactOutput π σ γ U j₀)) = p ∧
          preparedInputQueries (resamplingExactWord π σ γ j₀) =
            2 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 1 ∧
          (preparedInputQueries (resamplingExactWord π σ γ j₀) : ℝ) ≤
            Real.pi / (2 * Real.sqrt (levelMass π σ γ)) + 2 ∧
          preparedDataQueries (resamplingExactWord π σ γ j₀) = 0 ∧
          preparedFixedGates (resamplingExactWord π σ γ j₀) =
            4 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 2

end Qatlib.Concepts.Waterfill.ExactResampling
