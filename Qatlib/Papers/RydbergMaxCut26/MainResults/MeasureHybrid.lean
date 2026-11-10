/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph

noncomputable def selectorMap {n : ℕ} {Ω : Type*} (H ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (ω : Ω) : Ω×Bool :=
  (ω,idealChoice H ρ σ ω)

theorem selector_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (H ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ)
    (hσ : Measurable (fun ω => energy H (σ ω))) : Measurable (selectorMap H ρ σ) := by
  apply measurable_id.prodMk
  exact Measurable.ite (measurableSet_le measurable_const hσ) measurable_const measurable_const

noncomputable def outputLaw {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ) :
    Measure (Ω×Bool) := μ.map (selectorMap H ρ σ)

theorem outputLaw_probability {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (_hσ : Measurable (fun ω => energy H (σ ω))) :
    IsProbabilityMeasure (outputLaw μ H ρ σ) := by
  unfold outputLaw; infer_instance

theorem output_energy_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (H ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ)
    (hσ : Measurable (fun ω => energy H (σ ω))) :
    Measurable (fun z : Ω×Bool => energy H (outputDensity ρ σ z)) := by
  have he : (fun z : Ω×Bool => energy H (outputDensity ρ σ z))=
      (fun z : Ω×Bool => if z.2=true then energy H ρ else energy H (σ z.1)) := by
    funext z
    cases h : z.2 <;> simp [outputDensity,h]
  rw [he]
  exact Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
      (hσ.comp measurable_fst)

theorem output_energy {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H ρ : Matrix (Reg n) (Reg n) ℂ) (σ : Ω → Matrix (Reg n) (Reg n) ℂ)
    (hσ : Measurable (fun ω => energy H (σ ω))) :
    (∫ z,energy H (outputDensity ρ σ z) ∂outputLaw μ H ρ σ)=
      ∫ ω,min (energy H ρ) (energy H (σ ω)) ∂μ := by
  rw [outputLaw,integral_map (selector_measurable H ρ σ hσ).aemeasurable
    (output_energy_measurable H ρ σ hσ).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => ideal_energy H ρ σ ω))

theorem output_expected_convex {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (hσ : Measurable (fun ω => energy H (σ ω)))
    (hi : Integrable (fun ω => energy H (σ ω)) μ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ z,energy H (outputDensity ρ σ z) ∂outputLaw μ H ρ σ) ≤
      p*energy H ρ+(1-p)*(∫ ω,energy H (σ ω) ∂μ) := by
  rw [output_energy μ H ρ σ hσ]
  have hm : Integrable (fun ω => min (energy H ρ) (energy H (σ ω))) μ := by
    have he : (fun ω => min (energy H ρ) (energy H (σ ω)))=
        (fun ω => (energy H ρ+energy H (σ ω)-|energy H ρ-energy H (σ ω)|)/2) := by
      funext ω
      rcases le_total (energy H ρ) (energy H (σ ω)) with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    rw [he]
    exact ((integrable_const (energy H ρ)).add hi |>.sub ((integrable_const (energy H ρ)).sub hi).abs).div_const 2
  have hu : Integrable (fun ω => p*energy H ρ+(1-p)*energy H (σ ω)) μ :=
    (integrable_const (p*energy H ρ)).add (hi.const_mul (1-p))
  have h := integral_mono hm hu (fun ω => min_le_mixture (energy H ρ) (energy H (σ ω)) p hp0 hp1)
  simpa only [integral_add (integrable_const _) (hi.const_mul (1-p)),integral_const,
    probReal_univ,one_smul,integral_const_mul] using h
end Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
