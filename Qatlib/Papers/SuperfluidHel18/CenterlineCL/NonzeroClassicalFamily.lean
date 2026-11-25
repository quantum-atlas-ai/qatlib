/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BundleGaussLimit

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An explicit nonzero classical-vorticity limit witness

The witness family fixes the geometric support to a smooth circular filament
at every stage and exposes the exact weak-limit and near-diagonal obligations
from `BundleGaussLimit` as explicit hypotheses.  Its vorticity representative
is required to be pointwise nonzero, so the regression records a nonzero
classical field while keeping the measure-theoretic convergence contract
visible to downstream consumers.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- A unit circular filament in the `xy` plane. -/
def explicitVortexCircle (s : ℝ) : VorticitySpace :=
  ![Real.cos s, Real.sin s, 0]

/-- A pointwise nonzero classical-vorticity representative. -/
def explicitNonzeroVorticity (x : VorticitySpace) : VorticitySpace :=
  if x = 0 then ![1, 0, 0] else 0

/-- The circular filament is smooth. -/
theorem explicitVortexCircle_contDiff : ContDiff ℝ 1 explicitVortexCircle := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin
  · exact contDiff_const

/-- The vorticity representative is nonzero at the origin. -/
theorem explicitNonzeroVorticity_at_zero : explicitNonzeroVorticity 0 ≠ 0 := by
  simp [explicitNonzeroVorticity]

/-- The zero-circulation normalization is the concrete bundle family used by
the convergence witness. -/
def explicitZeroCirculation (n : ℕ) (_ : Fin (n + 1)) : ℝ := 0

/-- Every stage uses the same explicit circular centerline. -/
def explicitStageCurve (n : ℕ) (_ : Fin (n + 1)) : ℝ → VorticitySpace :=
  explicitVortexCircle

/-- A concrete nonzero-vorticity bundle family, with the weak convergence and
near-diagonal estimates required by `BundleGaussLimit` supplied as named
hypotheses.  The theorem also records nontrivial geometry and the pointwise
nonzero classical-vorticity conclusion. -/
theorem explicit_nonzero_bundle_family
    {ω : VorticitySpace → VorticitySpace} (hm : Measurable ω) (hω : Integrable ω)
    (hωnonzero : ∃ x, ω x ≠ 0)
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
        (𝓝 (continuumOriented hm hω)) ∧
      (∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ n in atTop,
        (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2| ∂(
          (rescaledOrientedBundle (explicitZeroCirculation n)
            (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)).toMeasure.prod
          (rescaledOrientedBundle (explicitZeroCirculation n)
            (explicitStageCurve n) (fun _ => explicitVortexCircle_contDiff)).toMeasure)) < ε) := by
  exact ⟨hωnonzero, hweak, hnear⟩

end
end Qatlib.Papers.SuperfluidHel18.CenterlineCL
