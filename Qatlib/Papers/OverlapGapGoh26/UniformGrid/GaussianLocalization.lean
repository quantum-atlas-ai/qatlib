/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy

/-!
# Gaussian localization for energy grids

Coordinates under `jointLaw` have the prescribed Gaussian marginal and subgaussian bound. Their
union bound controls escape from `dataBox` and makes the localization term in the adaptive
energy-grid reduction explicit for the random tensors of [GohMuller2026].

## Main statements

* `actual_dataBox_tail`: the data-box complement has an explicit Gaussian tail bound.
* `actual_gaussian_adaptive_grid`: a finite energy grid yields a probability reduction with that
  tail.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization

instance jointLaw_probability (M : ℝ) (v : NNReal) (r N : ℕ) :
    IsProbabilityMeasure (jointLaw M v r N) := by
  unfold jointLaw
  infer_instance

/-- Either sampled tensor coordinate under `jointLaw` has centered Gaussian law with variance
`(N^r)⁻¹`. -/
theorem joint_coordinate_preserving {r N : ℕ} (M : ℝ) (v : NNReal)
    (b : Bool) (k : Fin (r+1) → Fin N) :
    MeasurePreserving (fun w : Sample r N => (if b then w.1.2 else w.1.1) k)
      (jointLaw M v r N) (gaussianReal 0 (((N:NNReal)^r)⁻¹)) := by
  have ho : MeasurePreserving (fun w : Sample r N => w.1) (jointLaw M v r N)
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)) := measurePreserving_fst
  have he := measurePreserving_eval
    (fun _ : Fin (r+1) → Fin N => gaussianReal 0 (((N:NNReal)^r)⁻¹)) k
  cases b
  · exact he.comp (measurePreserving_fst.comp ho)
  · exact he.comp (measurePreserving_snd.comp ho)

/-- Either sampled tensor coordinate under `jointLaw` has a subgaussian
moment-generating-function bound with parameter `(N^r)⁻¹`. -/
theorem joint_coordinate_subgaussian {r N : ℕ} (M : ℝ) (v : NNReal)
    (b : Bool) (k : Fin (r+1) → Fin N) :
    HasSubgaussianMGF (fun w : Sample r N => (if b then w.1.2 else w.1.1) k)
      (((N:NNReal)^r)⁻¹) (jointLaw M v r N) := by
  have hp := joint_coordinate_preserving M v b k
  have hg := gaussian_id_subgaussian (((N:NNReal)^r)⁻¹)
  rw [← hp.map_eq] at hg
  simpa only [Function.comp_def, id_eq] using
    (HasSubgaussianMGF.of_map (X:=id)
      (Y:=fun w : Sample r N => (if b then w.1.2 else w.1.1) k)
      (μ:=jointLaw M v r N) (c:=((N:NNReal)^r)⁻¹) hp.measurable.aemeasurable hg)

/-- For nonnegative `M` and `R`, the real probability of leaving `dataBox r N R M` is at most `4
* N^(r + 1) * exp (−R² / (2 * (N^r)⁻¹))`. -/
theorem actual_dataBox_tail {r N : ℕ} (M : ℝ) (hM : 0≤M) (v : NNReal)
    (R : ℝ) (hR : 0≤R) :
    (jointLaw M v r N).real (dataBox r N R M)ᶜ ≤
      4*(N:ℝ)^(r+1)*Real.exp (-R^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
  let P := jointLaw M v r N
  let bad : Bool × (Fin (r+1) → Fin N) → Set (Sample r N) :=
    fun j => {w | R≤|(if j.1 then w.1.2 else w.1.1) j.2|}
  let seedBad : Set (Sample r N) := {w | ¬ ∀ i, w.2 i∈Set.Icc (-M) M}
  have hseed : P seedBad=0 := by
    have hp : MeasurePreserving (fun w : Sample r N => w.2) P (boundedSeedLaw M N v) :=
        measurePreserving_snd
    exact ae_iff.mp (hp.quasiMeasurePreserving.ae (boundedSeedLaw_ae M hM N v))
  have he : (dataBox r N R M)ᶜ ⊆ (⋃ j, bad j) ∪ seedBad := by
    intro w hw
    by_cases hs : ∀ i,w.2 i∈Set.Icc (-M) M
    · left
      by_contra hf
      have hab : ∀ b : Bool, ∀ k : Fin (r+1) → Fin N,
          (if b then w.1.2 else w.1.1) k∈Set.Icc (-R) R := by
        intro b k
        have hn : ¬ R≤|(if b then w.1.2 else w.1.1) k| := by
          intro hh
          exact hf (Set.mem_iUnion.mpr ⟨(b,k),hh⟩)
        exact ⟨le_of_lt (abs_lt.mp (lt_of_not_ge hn)).1,
          le_of_lt (abs_lt.mp (lt_of_not_ge hn)).2⟩
      exact hw ⟨⟨hab false,hab true⟩,hs⟩
    · exact Or.inr hs
  have hu := (measureReal_mono (μ:=P) he).trans (measureReal_union_le _ _)
  have hz : P.real seedBad=0 := (measureReal_eq_zero_iff).mpr hseed
  rw [hz,add_zero] at hu
  refine hu.trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc
    (∑ j : Bool × (Fin (r+1) → Fin N), P.real (bad j)) ≤
        ∑ _j : Bool × (Fin (r+1) → Fin N),
          2*Real.exp (-R^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
      apply Finset.sum_le_sum
      intro j _
      exact subgaussian_abs_tail (joint_coordinate_subgaussian M v j.1 j.2) R hR
    _ = 4*(N:ℝ)^(r+1)*Real.exp (-R^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring

/-- For nonnegative box radii and positive `ε`, a finite grid bounds continuum energy
exceedances by the explicit Gaussian localization tail plus the sum of grid exceedance
probabilities. -/
theorem actual_gaussian_adaptive_grid {r N : ℕ} (M : ℝ) (hM : 0≤M) (v : NNReal)
    (R : ℝ) (hR : 0≤R) (s : ℕ → ℝ) (T : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ S : Finset ℝ, (∀ σ∈S, σ∈Set.Icc (0:ℝ) 1) ∧ ∀ c : ℝ,
      jointLaw M v r N {w | ∃ τ∈Set.Icc (0:ℝ) 1, c+ε≤energyPath M s T w τ} ≤
        ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-R^2/(2*(((N:NNReal)^r)⁻¹:ℝ))))+
          ∑ σ∈S, jointLaw M v r N {w | c≤energyPath M s T w σ} := by
  obtain ⟨S,hS,hgrid⟩ := gaussian_adaptive_grid_reduction M R v s T ε hε
  refine ⟨S,hS,fun c => (hgrid c).trans (add_le_add ?_ le_rfl)⟩
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    (actual_dataBox_tail M hM v R hR)

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization
