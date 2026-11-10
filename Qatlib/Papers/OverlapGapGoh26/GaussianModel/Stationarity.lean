/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.GaussianLocalization
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity

theorem scalar_interpolation_map (v : NNReal) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun p : ℝ×ℝ => Real.sqrt (1-τ)*p.1+Real.sqrt τ*p.2)=gaussianReal 0 v := by
  let a := Real.sqrt (1-τ)
  let b := Real.sqrt τ
  have ha : a^2=1-τ := Real.sq_sqrt (by linarith [hτ.2])
  have hb : b^2=τ := Real.sq_sqrt hτ.1
  have hf : MeasurePreserving (fun p : ℝ×ℝ => a*p.1)
      ((gaussianReal 0 v).prod (gaussianReal 0 v))
      (gaussianReal (a*0) ((NNReal.mk (a^2) (sq_nonneg _))*v)) :=
    (show MeasurePreserving (fun x : ℝ => a*x) (gaussianReal 0 v)
      (gaussianReal (a*0) ((NNReal.mk (a^2) (sq_nonneg _))*v)) from
        ⟨by fun_prop,gaussianReal_map_const_mul a⟩).comp measurePreserving_fst
  have hg : MeasurePreserving (fun p : ℝ×ℝ => b*p.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v))
      (gaussianReal (b*0) ((NNReal.mk (b^2) (sq_nonneg _))*v)) :=
    (show MeasurePreserving (fun x : ℝ => b*x) (gaussianReal 0 v)
      (gaussianReal (b*0) ((NNReal.mk (b^2) (sq_nonneg _))*v)) from
        ⟨by fun_prop,gaussianReal_map_const_mul b⟩).comp measurePreserving_snd
  have hi : IndepFun (fun p : ℝ×ℝ => a*p.1) (fun p : ℝ×ℝ => b*p.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := indepFun_prod (by fun_prop) (by fun_prop)
  have he :=
      gaussianReal_add_gaussianReal_of_indepFun hi ⟨hf.measurable.aemeasurable,
      hf.map_eq⟩ ⟨hg.measurable.aemeasurable, hg.map_eq⟩
  have hv : (NNReal.mk (a^2) (sq_nonneg _))*v+(NNReal.mk (b^2) (sq_nonneg _))*v=v := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk]
    rw [ha,hb]
    ring
  simpa only [Pi.add_apply,mul_zero,zero_add,hv] using! he

theorem interpolate_preserving (r N : ℕ) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    MeasurePreserving (fun p : Tensor (r+1) N × Tensor (r+1) N => interpolate p.1 p.2 τ)
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)) (gaussianTensorLaw r N) := by
  let v : NNReal := ((N:NNReal)^r)⁻¹
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (r+1) → Fin N)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (r+1) → Fin N)
    (fun _ => gaussianReal 0 v) (fun _ => gaussianReal 0 v)
  have hm : MeasurePreserving
      (fun w : (Fin (r+1) → Fin N) → ℝ×ℝ => fun k => Real.sqrt (1-τ)*(w k).1+Real.sqrt τ*(w k).2)
      (Measure.pi (fun _ => (gaussianReal 0 v).prod (gaussianReal 0 v)))
      (gaussianTensorLaw r N) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.pi_map_pi (f:=fun _ (p : ℝ×ℝ) => Real.sqrt (1-τ)*p.1+Real.sqrt τ*p.2) (fun _ => by fun_prop)]
    simp_rw [scalar_interpolation_map v τ hτ]
    rfl
  exact hm.comp (MeasurePreserving.symm e he)

theorem interpolate_seed_preserving (M : ℝ) (v : NNReal) (r N : ℕ)
    (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    MeasurePreserving (fun w : Sample r N => (interpolate w.1.1 w.1.2 τ,w.2))
      (jointLaw M v r N) ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v)) :=
  (interpolate_preserving r N τ hτ).prod (MeasurePreserving.id _)

theorem actual_adaptive_energy_stationary {r N : ℕ} (M : ℝ) (v : NNReal)
    (s : ℕ → ℝ) (T : ℕ) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (c : ℝ) :
    jointLaw M v r N {w | c≤energyPath M s T w τ}=
      ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
        {p | c≤tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
  let E := fun p : Tensor (r+1) N × (Fin N → ℝ) =>
    tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)
  have hc : Continuous E := by
    have hj : Continuous (fun p : Tensor (r+1) N × (Fin N → ℝ) => rowTensor p.1) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro k
      exact (continuous_apply (@Fin.cons r (fun _ => Fin N) i k)).comp continuous_fst
    exact (continuous_tensorEnergy.comp (continuous_fst.prodMk
      ((continuous_ampOutput M s T).comp (hj.prodMk continuous_snd)))).div_const _
  exact (interpolate_seed_preserving M v r N τ hτ).measure_preimage
    (measurableSet_le measurable_const hc.measurable).nullMeasurableSet

theorem actual_fixed_instance_grid_reduction {r N : ℕ} (M : ℝ) (hM : 0≤M) (v : NNReal)
    (R : ℝ) (hR : 0≤R) (s : ℕ → ℝ) (T : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ S : Finset ℝ, (∀ σ∈S, σ∈Set.Icc (0:ℝ) 1) ∧ ∀ c : ℝ,
      jointLaw M v r N {w | ∃ τ∈Set.Icc (0:ℝ) 1, c+ε≤energyPath M s T w τ} ≤
        ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-R^2/(2*(((N:NNReal)^r)⁻¹:ℝ))))+
          S.card * ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
            {p | c≤tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
  obtain ⟨S,hS,hb⟩ := actual_gaussian_adaptive_grid M hM v R hR s T ε hε
  refine ⟨S,hS,?_⟩
  intro c
  convert! hb c using 1
  congr 1
  have he : (∑ σ∈S,jointLaw M v r N {w | c≤energyPath M s T w σ})=
      ∑ _σ∈S,((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
        {p | c≤tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact actual_adaptive_energy_stationary M v s T σ (hS σ hσ) c
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul]

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
