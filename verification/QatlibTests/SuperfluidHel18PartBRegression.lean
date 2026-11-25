/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.NonzeroClassicalFamily
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.WeightedPhaseCancellation

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace QatlibTests.SuperfluidHel18PartBRegression

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Qatlib.Papers.SuperfluidHel18.SeifertCWF

local notation "VorticitySpace" => Fin 3 → ℝ

/-- A two-component phase-defect witness with nonzero weighted terms and
opposite punctured-domain boundary fluxes. -/
example :
    weightedCWFDefect (![1, 2] : Fin 2 → ℝ)
      (fun _ _ => 0) (![1, 0] : Fin 2 → ℝ) (![0, -(1 / 4)] : Fin 2 → ℝ) = 0 := by
  let κ : Fin 2 → ℝ := ![1, 2]
  let link : Fin 2 → Fin 2 → ℝ := fun _ _ => 0
  let wr : Fin 2 → ℝ := ![1, 0]
  let tw : Fin 2 → ℝ := ![0, -(1 / 4)]
  let boundary : Fin 2 → ℝ := fun i => weightedCWFComponent κ link wr tw i
  have hdata : RegularSeifertPhaseJumpData κ link wr tw :=
    { phaseJump := fun i => 2 * Real.pi * κ i
      boundaryFlux := boundary
      regular_phase_jump := by intro i; rfl
      nonzero_phase_jump := by
        intro i
        fin_cases i <;> simp [κ, Real.pi_ne_zero]
      component_flux := by
        intro i
        fin_cases i
        · simp [boundary, κ, link, wr, tw, weightedCWFComponent]
        · simp [boundary, κ, link, wr, tw, weightedCWFComponent]
          ring
      punctured_boundary_flux_zero := by
        simp [boundary, κ, link, wr, tw, weightedCWFComponent]
        norm_num }
  simpa [κ, link, wr, tw] using weighted_cwf_phase_defect_cancel κ link wr tw hdata

/-- The geometric family is nontrivial at every stage through its smooth
circular centerline, and the classical-vorticity witness is nonzero. -/
example : explicitNonzeroVorticity 0 ≠ 0 :=
  explicitNonzeroVorticity_at_zero

example : ContDiff ℝ 1 explicitVortexCircle :=
  explicitVortexCircle_contDiff

example (ω : VorticitySpace → VorticitySpace) (hm : Measurable ω)
    (hω : Integrable ω) (hωnonzero : ∃ x, ω x ≠ 0)
    (hweak : Tendsto (fun n => rescaledOrientedBundle (explicitZeroCirculation n)
      (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)) atTop
      (𝓝 (continuumOriented hm hω)))
    (hnear : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ n in atTop,
      (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
        (rescaledOrientedBundle (explicitZeroCirculation n)
          (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)).toMeasure.prod
        (rescaledOrientedBundle (explicitZeroCirculation n)
          (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)).toMeasure)) < ε) :
    (∃ x, ω x ≠ 0) ∧
      Tendsto (fun n => rescaledOrientedBundle (explicitZeroCirculation n)
        (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)) atTop
        (𝓝 (continuumOriented hm hω)) := by
  obtain ⟨hnz, hw, _⟩ := explicit_nonzero_bundle_family hm hω hωnonzero hweak hnear
  exact ⟨hnz, hw⟩

end QatlibTests.SuperfluidHel18PartBRegression
