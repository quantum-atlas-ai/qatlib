/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.DensityMargin

/-!
# Overlap gap obstructions for spin readout paths

The spin readout path inherits the continuous overlap crossing argument in both total energy and
density units. `spinUniformNear_subset_failures` expresses uniform energy proximity as a subset
of overlap gap, nonzero path, or endpoint decorrelation failures, and
`gaussian_spin_uniform_success_le_failures` bounds its Gaussian probability. These statements
connect the spin dynamics to the conditional obstruction associated with [GohMuller2026].

## Main statements

* `actual_spin_density_obstruction`: For `N > 0`, the density ensemble overlap gap condition
  with `ν₁ < ν₂ < 1` forces a nonzero spin path with endpoint overlap at most `ν₁` to exceed the
  interpolated cube minimum density plus `μ` somewhere. See [GohMuller2026].
* `gaussian_spin_uniform_success_le_failures`: For `ν₁ < ν₂ < 1`, the `jointLaw` probability of
  uniform spin energy proximity is at most the sum of the overlap gap, nonzero path, and
  endpoint decorrelation failure probabilities.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.SpinObstruction

/-- Under the ensemble overlap gap condition with `ν₁ < ν₂ < 1`, a nonzero spin path with
endpoint overlap at most `ν₁` exceeds the interpolated cube minimum plus `μ` at some
parameter. See [GohMuller2026]. -/
theorem actual_spin_ogp_obstruction {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (μ ν₁ ν₂ : ℝ)
    (hogp : ensembleOGP A B μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hnz : ∀ τ ∈ Set.Icc (0:ℝ) 1, spinPath M s T A B seed τ≠0)
    (hdec : normalizedOverlap (spinPath M s T A B seed 0) (spinPath M s T A B seed 1)≤ν₁) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1,
      cubeOpt (interpolate A B τ)+μ <
        tensorEnergy (interpolate A B τ) (spinPath M s T A B seed τ).ofLp := by
  by_contra hn
  push Not at hn
  obtain ⟨τ,hτ,hlo,hhi⟩ := actual_overlap_gap_crossing (spinPath M s T A B seed)
    (continuous_spinPath M s T A B seed).continuousOn hnz ν₁ ν₂ hgap hhigh hdec
  have hz : (0:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := hogp 0 hz τ hτ _ _
    (fun i => spinPath_cube M s T A B seed 0 i)
    (fun i => spinPath_cube M s T A B seed τ i) (hn 0 hz) (hn τ hτ)
  rcases hb with hb | hb <;> linarith

/-- For `N > 0`, the density ensemble overlap gap condition with `ν₁ < ν₂ < 1` forces a nonzero
spin path with endpoint overlap at most `ν₁` to exceed the interpolated cube minimum density
plus `μ` somewhere. See [GohMuller2026]. -/
theorem actual_spin_density_obstruction {r N : ℕ} (hN : 0<N)
    (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (A B : Tensor (r+1) N)
    (seed : Fin N → ℝ) (μ ν₁ ν₂ : ℝ)
    (hogp : densityEnsembleOGP A B μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hnz : ∀ τ ∈ Set.Icc (0:ℝ) 1, spinPath M s T A B seed τ≠0)
    (hdec : normalizedOverlap (spinPath M s T A B seed 0) (spinPath M s T A B seed 1)≤ν₁) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1,
      cubeOpt (interpolate A B τ)/(N:ℝ)+μ <
        tensorEnergy (interpolate A B τ) (spinPath M s T A B seed τ).ofLp/(N:ℝ) := by
  have hraw := (density_ogp_iff_total hN A B μ ν₁ ν₂).mp hogp
  obtain ⟨τ,hτ,he⟩ :=
      actual_spin_ogp_obstruction M s T A B seed ((N:ℝ)*μ) ν₁ ν₂ hraw hgap hhigh hnz hdec
  refine ⟨τ,hτ,?_⟩
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := (div_lt_div_of_pos_right he hn)
  convert! h using 1; field_simp

/-- The event that the spin readout energy stays at most `μ` above the interpolated cube minimum
throughout `[0,1]`. -/
def spinUniformNearEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (μ : ℝ) : Set (Sample r N) :=
  {w | ∀ τ∈Set.Icc (0:ℝ) 1,
    tensorEnergy (interpolate w.1.1 w.1.2 τ) (spinPath M s T w.1.1 w.1.2 w.2 τ).ofLp≤
      cubeOpt (interpolate w.1.1 w.1.2 τ)+μ}

/-- The event that the spin readout path is nonzero at every interpolation parameter in `[0,1]`. -/
def spinNonzeroEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) : Set (Sample r N) :=
  {w | ∀ τ∈Set.Icc (0:ℝ) 1,spinPath M s T w.1.1 w.1.2 w.2 τ≠0}

/-- The event that the spin readout endpoints have normalized overlap at most `ν`. -/
def spinDecorrelationEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (ν : ℝ) : Set (Sample r N) :=
  {w | normalizedOverlap (spinPath M s T w.1.1 w.1.2 w.2 0)
      (spinPath M s T w.1.1 w.1.2 w.2 1)≤ν}

/-- For `ν₁ < ν₂ < 1`, uniform spin energy proximity implies failure of the ensemble overlap
gap, the nonzero path condition, or endpoint decorrelation at threshold `ν₁`. -/
theorem spinUniformNear_subset_failures {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (μ ν₁ ν₂ : ℝ) (hgap : ν₁<ν₂) (hhigh : ν₂<1) :
    spinUniformNearEvent (r:=r) (N:=N) M s T μ ⊆
      (ogpEvent μ ν₁ ν₂)ᶜ ∪ (spinNonzeroEvent M s T)ᶜ ∪ (spinDecorrelationEvent M s T ν₁)ᶜ := by
  intro w hw
  by_cases ho : w∈ogpEvent μ ν₁ ν₂
  · by_cases hn : w∈spinNonzeroEvent M s T
    · by_cases hd : w∈spinDecorrelationEvent M s T ν₁
      · obtain ⟨τ,hτ,hbad⟩ := actual_spin_ogp_obstruction M s T w.1.1 w.1.2 w.2 μ ν₁ ν₂ ho hgap hhigh hn hd
        exact False.elim (not_lt_of_ge (hw τ hτ) hbad)
      · exact Or.inr hd
    · exact Or.inl (Or.inr hn)
  · exact Or.inl (Or.inl ho)

/-- For `ν₁ < ν₂ < 1`, the `jointLaw` probability of uniform spin energy proximity is at most
the sum of the overlap gap, nonzero path, and endpoint decorrelation failure probabilities.
See [GohMuller2026]. -/
theorem gaussian_spin_uniform_success_le_failures {r N : ℕ} (M : ℝ) (v : NNReal)
    (s : ℕ → ℝ) (T : ℕ) (μ ν₁ ν₂ : ℝ) (hgap : ν₁<ν₂) (hhigh : ν₂<1) :
    jointLaw M v r N (spinUniformNearEvent M s T μ)≤
      jointLaw M v r N (ogpEvent μ ν₁ ν₂)ᶜ+
        jointLaw M v r N (spinNonzeroEvent M s T)ᶜ+
          jointLaw M v r N (spinDecorrelationEvent M s T ν₁)ᶜ :=
  (measure_mono (spinUniformNear_subset_failures M s T μ ν₁ ν₂ hgap hhigh)).trans
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.SpinObstruction
