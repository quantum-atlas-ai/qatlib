/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.SpinObstruction
import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.MaximizingSpin

theorem interpolate_neg {q N : ℕ} (J K : Tensor q N) (τ : ℝ) :
    interpolate (-J) (-K) τ= -(interpolate J K τ) := by
  ext k
  unfold interpolate
  simp only [Pi.neg_apply]
  ring

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
