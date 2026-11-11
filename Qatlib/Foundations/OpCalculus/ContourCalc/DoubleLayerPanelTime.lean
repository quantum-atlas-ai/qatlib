/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-! The compact [-1,1] parameter space has its actual restricted Lebesgue
measure (mass two). Finite label/product integrals preserve the original
panel integrals, including their normalization. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open MeasureTheory
open scoped BigOperators NNReal

/-- Abbreviation for Panel Time in the double layer panel time model. -/
abbrev PanelTime : Type := Set.Icc (-1 : ℝ) 1
noncomputable instance : MeasureSpace PanelTime := Measure.Subtype.measureSpace

/-- The identity or estimate `panelTime_volume` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panelTime_volume : (volume : Measure PanelTime) Set.univ=2 := by
  rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc,Real.volume_Icc]
  norm_num

instance : IsFiniteMeasure (volume : Measure PanelTime) where
  measure_univ_lt_top := by rw [panelTime_volume]; norm_num

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The identity or estimate `panelTime_integral` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panelTime_integral (f : ℝ → B) :
    (∫ s : PanelTime,f (s : ℝ))=∫ t in (-1 : ℝ)..1,f t := by
  rw [integral_subtype measurableSet_Icc]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ)≤1)]
  exact integral_Icc_eq_integral_Ioc

variable [CompleteSpace B]

/-- The identity or estimate `finite_label_integral` holds with the displayed separation, geometry and norm hypotheses. -/
theorem finite_label_integral (N : ℕ) (F : C(Fin N × PanelTime,B)) :
    (∫ p,F p ∂(Measure.count.prod (volume : Measure PanelTime)))=
      ∑ j : Fin N,∫ t : PanelTime,F (j,t) := by
  have hF : Integrable F (Measure.count.prod (volume : Measure PanelTime)) :=
    memLp_one_iff_integrable.mp (F.memLp (p := 1) (μ := Measure.count.prod (volume : Measure PanelTime)) ℝ)
  rw [integral_prod _ hF,integral_count]

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer

namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open MeasureTheory
open scoped BigOperators NNReal

/-- Moving the common positive density coefficient into the measure avoids
an additional square-root normalization in each Gram row. -/
def dilationWeight : ℝ≥0 := ⟨(4*Real.pi)⁻¹,inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)⟩

/-- Construction for dilation Measure in the double layer panel time model. -/
def dilationMeasure (N : ℕ) : Measure (Fin N × PanelTime) :=
  dilationWeight • ((Measure.count : Measure (Fin N)).prod (volume : Measure PanelTime))

instance (N : ℕ) : IsFiniteMeasure (dilationMeasure N) := by
  unfold dilationMeasure
  infer_instance

/-- The identity or estimate `dilationMeasure_integral` holds with the displayed separation, geometry and norm hypotheses. -/
theorem dilationMeasure_integral {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (N : ℕ) (F : C(Fin N × PanelTime,B)) :
    (∫ p,F p ∂dilationMeasure N)=(4*Real.pi)⁻¹ • (∑ j : Fin N,∫ t : PanelTime,F (j,t)) := by
  rw [dilationMeasure,integral_smul_nnreal_measure,finite_label_integral]
  rfl

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
