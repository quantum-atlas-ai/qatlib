/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.GaussianObstruction

/-!
# Energy density margins in overlap gap obstructions

`densityEnsembleOGP` states the ensemble overlap gap condition using energy per coordinate. For
positive dimension, `density_ogp_iff_total` identifies it with the total energy condition at
margin `Nμ`, and `source_density_path_obstruction` transfers the continuous AMP path obstruction
to density units. This keeps the margin convention explicit in the analysis associated with
[GohMuller2026].

## Main statements

* `density_ogp_iff_total`: For `N > 0`, the density ensemble overlap gap condition at margin `μ`
  is equivalent to the total energy ensemble condition at margin `Nμ`.
* `source_density_path_obstruction`: For `N > 0`, the density ensemble overlap gap condition
  with `ν₁ < ν₂ < 1` forces a nonzero AMP path with endpoint overlap at most `ν₁` to exceed the
  cube minimum density plus `μ` somewhere on `[0,1]`. See [GohMuller2026].

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density

/-- For `n > 0`, the density inequality `e/n ≤ opt/n + μ` is equivalent to the total energy
inequality `e ≤ opt + nμ`. -/
theorem density_near_iff_raw {n : ℝ} (hn : 0<n) (e opt μ : ℝ) :
    e/n≤opt/n+μ ↔ e≤opt+n*μ := by
  have he : opt/n+μ=(opt+n*μ)/n := by field_simp
  rw [he, div_le_div_iff_of_pos_right hn]

/-- The ensemble overlap gap condition for cube vectors whose energy densities are within `μ` of
the respective interpolated cube minimum densities. -/
def densityEnsembleOGP {q N : ℕ} (A B : Tensor q N) (μ ν₁ ν₂ : ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc (0:ℝ) 1,
    ∀ (u v : EuclideanSpace ℝ (Fin N)), u.ofLp ∈ hilbertCube N → v.ofLp ∈ hilbertCube N →
      tensorEnergy (interpolate A B τ) u.ofLp/(N:ℝ)≤cubeOpt (interpolate A B τ)/(N:ℝ)+μ →
      tensorEnergy (interpolate A B σ) v.ofLp/(N:ℝ)≤cubeOpt (interpolate A B σ)/(N:ℝ)+μ →
      normalizedOverlap u v≤ν₁ ∨ ν₂≤normalizedOverlap u v

/-- For `N > 0`, the density ensemble overlap gap condition at margin `μ` is equivalent to the
total energy ensemble condition at margin `Nμ`. See [GohMuller2026]. -/
theorem density_ogp_iff_total {q N : ℕ} (hN : 0<N) (A B : Tensor q N) (μ ν₁ ν₂ : ℝ) :
    densityEnsembleOGP A B μ ν₁ ν₂ ↔ ensembleOGP A B ((N:ℝ)*μ) ν₁ ν₂ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  simp only [densityEnsembleOGP, ensembleOGP, density_near_iff_raw hn]

/-- For `N > 0`, the density ensemble overlap gap condition with `ν₁ < ν₂ < 1` forces a nonzero
AMP path with endpoint overlap at most `ν₁` to exceed the cube minimum density plus `μ`
somewhere on `[0,1]`. See [GohMuller2026]. -/
theorem source_density_path_obstruction {r N : ℕ} (hN : 0<N) (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (μ ν₁ ν₂ : ℝ)
    (hogp : densityEnsembleOGP A B μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hnz : ∀ τ ∈ Set.Icc (0:ℝ) 1, outputPath M s T A B seed τ≠0)
    (hdec : normalizedOverlap (outputPath M s T A B seed 0) (outputPath M s T A B seed 1)≤ν₁) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1,
      cubeOpt (interpolate A B τ)/(N:ℝ)+μ <
        tensorEnergy (interpolate A B τ) (outputPath M s T A B seed τ).ofLp/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  obtain ⟨τ,hτ,hbad⟩ := actual_amp_ogp_obstruction M s T A B seed ((N:ℝ)*μ) ν₁ ν₂
    ((density_ogp_iff_total hN A B μ ν₁ ν₂).mp hogp) hgap hhigh hnz hdec
  refine ⟨τ,hτ,?_⟩
  have he : cubeOpt (interpolate A B τ)/(N:ℝ)+μ=
      (cubeOpt (interpolate A B τ)+(N:ℝ)*μ)/(N:ℝ) := by field_simp
  rw [he]
  exact (div_lt_div_iff_of_pos_right hn).mpr hbad

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density
