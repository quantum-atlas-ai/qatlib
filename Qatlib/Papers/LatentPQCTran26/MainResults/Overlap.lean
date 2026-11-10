/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.Overlap

def gradRichSet {Θ : Type*} (F : Θ → ℝ) (c : ℝ) : Set Θ :=
  {θ | c ≤ F θ}

theorem integral_ge_mul_measure
    {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsFiniteMeasure μ]
    (F : Θ → ℝ) (c : ℝ) (hS : MeasurableSet (gradRichSet F c))
    (hF_int : Integrable F μ) (hF_nonneg : ∀ θ, 0 ≤ F θ) :
    c * μ.real (gradRichSet F c) ≤ ∫ θ, F θ ∂μ := by
  have hconst_int : IntegrableOn (fun _ : Θ => c) (gradRichSet F c) μ :=
    (integrable_const c).integrableOn
  have hF_on : IntegrableOn F (gradRichSet F c) μ := hF_int.integrableOn
  have hmono : ∫ θ in gradRichSet F c, (fun _ : Θ => c) θ ∂μ ≤
      ∫ θ in gradRichSet F c, F θ ∂μ :=
    setIntegral_mono_on hconst_int hF_on hS (fun θ hθ => hθ)
  have hconst : ∫ θ in gradRichSet F c, (fun _ : Θ => c) θ ∂μ =
      c * μ.real (gradRichSet F c) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hle : ∫ θ in gradRichSet F c, F θ ∂μ ≤ ∫ θ, F θ ∂μ :=
    setIntegral_le_integral hF_int (Filter.Eventually.of_forall hF_nonneg)
  rw [← hconst]
  exact le_trans hmono hle

theorem pushforward_integral
    {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (r : Measure Z) (f : Z → Θ) (hf : AEMeasurable f r)
    (F : Θ → ℝ) (hF : AEStronglyMeasurable F (Measure.map f r)) :
    ∫ z, F (f z) ∂r = ∫ θ, F θ ∂(Measure.map f r) :=
  (integral_map hf hF).symm

theorem lemma11_overlap_lower_bound
    {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ] [NormedAddCommGroup Θ]
    (r : Measure Z) (f : Z → Θ) (hf : AEMeasurable f r)
    [IsFiniteMeasure (Measure.map f r)]
    (grad : Θ → Θ) (c : ℝ)
    (hS : MeasurableSet (gradRichSet (fun θ => (‖grad θ‖) ^ 2) c))
    (hF_int : Integrable (fun θ => (‖grad θ‖) ^ 2) (Measure.map f r))
    (hF_meas : AEStronglyMeasurable (fun θ => (‖grad θ‖) ^ 2) (Measure.map f r)) :
    c * (Measure.map f r).real (gradRichSet (fun θ => (‖grad θ‖) ^ 2) c)
      ≤ ∫ z, (‖grad (f z)‖) ^ 2 ∂r := by
  have heq : ∫ z, (‖grad (f z)‖) ^ 2 ∂r
      = ∫ θ, (‖grad θ‖) ^ 2 ∂(Measure.map f r) :=
    pushforward_integral r f hf (fun θ => (‖grad θ‖) ^ 2) hF_meas
  rw [heq]
  exact integral_ge_mul_measure _ _ c hS hF_int (fun θ => sq_nonneg _)

end Qatlib.Papers.LatentPQCTran26.MainResults.Overlap
