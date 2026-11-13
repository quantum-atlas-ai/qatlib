/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.SpinObstruction
import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention

/-!
# Overlap gap obstructions for maximizing spin energies

`interpolate_neg` identifies tensor interpolation under simultaneous sign reversal. Applying the
overlap gap condition to the negated tensors gives `actual_maximizing_spin_obstruction`: a
continuous nonzero spin path with decorrelated endpoints must fall below the cube maximum by
more than the prescribed margin somewhere. This states the maximizing energy form of the
obstruction associated with [GohMuller2026].

## Main statements

* `interpolate_neg`: Interpolating two negated tensors gives the negative of their
  interpolation.
* `actual_maximizing_spin_obstruction`: If the negated tensor pair satisfies the ensemble
  overlap gap condition with `ν₁ < ν₂ < 1`, then a nonzero spin path with endpoint overlap at
  most `ν₁` has energy strictly below the interpolated cube maximum minus `μ` at some parameter.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.MaximizingSpin

/-- Interpolating two negated tensors gives the negative of their interpolation. -/
theorem interpolate_neg {q N : ℕ} (J K : Tensor q N) (τ : ℝ) :
    interpolate (-J) (-K) τ= -(interpolate J K τ) := by
  ext k
  unfold interpolate
  simp only [Pi.neg_apply]
  ring

/-- If the negated tensor pair satisfies the ensemble overlap gap condition with `ν₁ < ν₂ < 1`,
then a nonzero spin path with endpoint overlap at most `ν₁` has energy strictly below the
interpolated cube maximum minus `μ` at some parameter. See [GohMuller2026]. -/
theorem actual_maximizing_spin_obstruction {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (J K : Tensor (r+1) N) (seed : Fin N → ℝ) (μ ν₁ ν₂ : ℝ)
    (hogp : ensembleOGP (-J) (-K) μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hnz : ∀ τ∈Set.Icc (0:ℝ) 1,spinPath M s T J K seed τ≠0)
    (hdec : normalizedOverlap (spinPath M s T J K seed 0) (spinPath M s T J K seed 1)≤ν₁) :
    ∃ τ∈Set.Icc (0:ℝ) 1,
      tensorEnergy (interpolate J K τ) (spinPath M s T J K seed τ).ofLp <
        -cubeOpt (-(interpolate J K τ))-μ := by
  by_contra hn
  push Not at hn
  have hnear (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
      tensorEnergy (interpolate (-J) (-K) τ) (spinPath M s T J K seed τ).ofLp≤
        cubeOpt (interpolate (-J) (-K) τ)+μ := by
    rw [interpolate_neg,tensor_energy_neg]
    have h := hn τ hτ
    linarith
  obtain ⟨τ,hτ,hlo,hhi⟩ := actual_overlap_gap_crossing (spinPath M s T J K seed)
    (continuous_spinPath M s T J K seed).continuousOn hnz ν₁ ν₂ hgap hhigh hdec
  have hz : (0:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := hogp 0 hz τ hτ _ _
    (fun i => spinPath_cube M s T J K seed 0 i)
    (fun i => spinPath_cube M s T J K seed τ i) (hnear 0 hz) (hnear τ hτ)
  rcases hb with hb|hb <;> linarith

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.MaximizingSpin
