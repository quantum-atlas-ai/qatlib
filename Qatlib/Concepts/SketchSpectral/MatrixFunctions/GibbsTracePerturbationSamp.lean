/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.GibbsTracePerturbationStat
import Qatlib.Concepts.SketchSpectral.MatrixFunctions.GibbsTraceLowerBoundSamp
set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem hermitian_exp_trace_bounds {I : Type} [Fintype I] [DecidableEq I]
    (H Ht : Matrix I I ℂ) (hH : H.IsHermitian) (hHt : Ht.IsHermitian) :
    Real.exp (-‖Ht-H‖) * (Matrix.trace (exp H)).re ≤ (Matrix.trace (exp Ht)).re ∧
    (Matrix.trace (exp Ht)).re ≤ Real.exp ‖Ht-H‖ * (Matrix.trace (exp H)).re := by
  rw [hermitian_exp_trace H hH, hermitian_exp_trace Ht hHt]
  have hw := (ordered_hermitian_weyl_and_hoffman_wielandt I Ht H hHt hH).1
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hw i)).1
    linarith
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hw i)).2
    linarith

theorem gibbsTracePerturbation : GibbsTracePerturbation := by
  intro I _ _ H Ht hH hHt
  have hb : 0 ≤ (Matrix.trace (exp H)).re := by
    rw [hermitian_exp_trace H hH]
    exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  obtain ⟨hl,hu⟩ := hermitian_exp_trace_bounds H Ht hH hHt
  have hc : 2 ≤ Real.exp ‖Ht-H‖ + Real.exp (-‖Ht-H‖) := by
    linarith [Real.add_one_le_exp ‖Ht-H‖, Real.add_one_le_exp (-‖Ht-H‖)]
  have hm := mul_le_mul_of_nonneg_right hc hb
  apply abs_le.mpr
  constructor <;> nlinarith
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
