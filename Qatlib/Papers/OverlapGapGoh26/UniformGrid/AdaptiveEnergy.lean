/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.GaussianObstruction

/-!
# Compact finite grids for AMP energy

`energyPath` evaluates the AMP energy density along tensor interpolation. Joint continuity and
compact data boxes give a finite interpolation grid, which reduces a continuum threshold event
to localization failure and finitely many grid events in the setting of [GohMuller2026].

## Main statements

* `actual_energy_finite_grid`: a finite grid approximates the energy uniformly on a data box.
* `gaussian_adaptive_grid_reduction`: a continuum event is bounded by a localization tail and
  grid probabilities.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy

/-- The tensor energy density of the AMP output along interpolation between the two sampled
tensors. -/
def energyPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (w : Sample r N) (τ : ℝ) : ℝ :=
  tensorEnergy (interpolate w.1.1 w.1.2 τ)
    (ampOutput M (rowTensor (interpolate w.1.1 w.1.2 τ)) w.2 s T)/(N:ℝ)

/-- The AMP energy path is jointly continuous in the sampled tensors, seed, and interpolation
parameter. -/
theorem continuous_energyPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : Sample r N × ℝ => energyPath M s T p.1 p.2) := by
  have hi : Continuous (fun p : Sample r N × ℝ => interpolate p.1.1.1 p.1.1.2 p.2) := by
    apply continuous_pi
    intro k
    unfold interpolate
    fun_prop
  have hj : Continuous (fun p : Sample r N × ℝ => rowTensor (interpolate p.1.1.1 p.1.1.2 p.2)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    exact (continuous_apply (Fin.cons i k)).comp hi
  have ho := (continuous_ampOutput M s T).comp
    (hj.prodMk (show Continuous (fun p : Sample r N × ℝ => p.1.2) from by fun_prop))
  exact ((continuous_tensorEnergy.comp (hi.prodMk ho)).div_const (N:ℝ))

/-- The set of samples whose two tensor arrays lie coordinatewise in `[−R, R]` and whose seed
lies coordinatewise in `[−M, M]`. -/
def dataBox (r N : ℕ) (R M : ℝ) : Set (Sample r N) :=
  ({A : Tensor (r+1) N | ∀ k,A k∈Set.Icc (-R) R} ×ˢ
    {B : Tensor (r+1) N | ∀ k,B k∈Set.Icc (-R) R}) ×ˢ
      {seed : Fin N → ℝ | ∀ i,seed i∈Set.Icc (-M) M}

/-- The data box is compact. -/
theorem isCompact_dataBox (r N : ℕ) (R M : ℝ) : IsCompact (dataBox r N R M) :=
  ((isCompact_pi_infinite (fun _ : Fin (r+1) → Fin N => isCompact_Icc)).prod
    (isCompact_pi_infinite (fun _ : Fin (r+1) → Fin N => isCompact_Icc))).prod
      (isCompact_pi_infinite (fun _ : Fin N => isCompact_Icc))

/-- For positive `ε`, a finite grid in `[0, 1]` approximates every energy path on the data box
to within `ε`, uniformly in the interpolation parameter. -/
theorem actual_energy_finite_grid {r N : ℕ} (M R : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ S : Finset ℝ, (∀ σ∈S, σ∈Set.Icc (0:ℝ) 1) ∧
      ∀ w∈dataBox r N R M, ∀ τ∈Set.Icc (0:ℝ) 1,
        ∃ σ∈S, |energyPath M s T w τ-energyPath M s T w σ|<ε := by
  have hK := (isCompact_dataBox r N R M).prod (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  have hu := hK.uniformContinuousOn_of_continuous (continuous_energyPath M s T).continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨S,hS,hfin,hcover⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).finite_cover_balls (half_pos hδ)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro σ hσ
    exact hS (hfin.mem_toFinset.mp hσ)
  · intro w hw τ hτ
    obtain ⟨σ,hσ⟩ := Set.mem_iUnion.mp (hcover hτ)
    obtain ⟨hσ,hball⟩ := Set.mem_iUnion.mp hσ
    refine ⟨σ,hfin.mem_toFinset.mpr hσ,?_⟩
    have hp : dist (w,τ) (w,σ)<δ := by
      have hdist : dist τ σ<δ/2 := hball
      simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using
          lt_trans hdist (half_lt_self hδ)
    simpa only [Real.dist_eq] using hd (w,τ) ⟨hw,hτ⟩ (w,σ) ⟨hw,hS hσ⟩ hp

/-- For positive `ε`, a finite grid bounds each continuum exceedance probability at level `c +
ε` by the data-box complement probability plus the sum of grid exceedance probabilities at
level `c`. -/
theorem gaussian_adaptive_grid_reduction {r N : ℕ} (M R : ℝ) (v : NNReal)
    (s : ℕ → ℝ) (T : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ S : Finset ℝ, (∀ σ∈S, σ∈Set.Icc (0:ℝ) 1) ∧ ∀ c : ℝ,
      jointLaw M v r N {w | ∃ τ∈Set.Icc (0:ℝ) 1, c+ε≤energyPath M s T w τ}≤
        jointLaw M v r N (dataBox r N R M)ᶜ+
          ∑ σ∈S, jointLaw M v r N {w | c≤energyPath M s T w σ} := by
  obtain ⟨S,hS,hu⟩ := actual_energy_finite_grid M R s T ε hε
  refine ⟨S,hS,?_⟩
  intro c
  have he : {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1, c+ε≤energyPath M s T w τ} ⊆
      (dataBox r N R M)ᶜ ∪ ⋃ σ∈S, {w | c≤energyPath M s T w σ} := by
    intro w hw
    by_cases hb : w∈dataBox r N R M
    · obtain ⟨τ,hτ,hbig⟩ := hw
      obtain ⟨σ,hσ,hd⟩ := hu w hb τ hτ
      right
      apply Set.mem_iUnion.mpr ⟨σ,?_⟩
      apply Set.mem_iUnion.mpr ⟨hσ,?_⟩
      have hdist := abs_lt.mp hd
      change c≤energyPath M s T w σ
      linarith [hdist.2]
    · exact Or.inl hb
  exact (measure_mono he).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le S _)))

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
