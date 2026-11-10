/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.KernelWitnessCorrectedStat
import Qatlib.Concepts.QueryComplexity.Reflections.WitnessLaws
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

theorem kernelWitnessCorrected : KernelWitnessCorrected := by
  intro X _ _ n m input f v W hd hW
  have hw : 0 < W := by linarith
  constructor
  · intro x hx
    refine ⟨source_positive_nonzero input f v W hW x,source_positive_kernel input f v W hd hW x hx,?_⟩
    change (9/10 : ℝ)*(∑ c,‖sourcePositiveWitness input f v W x c‖^2) ≤ ‖((-3*Real.sqrt W : ℝ) : ℂ)‖^2
    rw [source_positive_norm input f v W hw.le x,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hw.le]
    norm_num
    nlinarith [hd.1 x]
  · intro x hx
    refine ⟨source_negative_nonzero input f v x hx,source_negative_kernel input f v x hx,?_⟩
    rw [source_negative_norm input f v x hx,source_negative_overlap input f v W x hx]
    rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    have he : (1/(3*Real.sqrt W))^2=1/(9*W) := by
      rw [div_pow,mul_pow,Real.sq_sqrt hw.le]
      norm_num
    rw [he]
    have hp : 0 ≤ 1/(9*W*(W+1)) := by positivity
    have hb:=mul_le_mul_of_nonneg_left (show 1+(∑ j,∑ k,‖v x j k‖^2) ≤ 1+W by linarith [hd.1 x]) hp
    have hr : 1/(9*W*(W+1))*(1+W)=1/(9*W) := by field_simp;ring
    simpa only [hr] using hb
end Qatlib.Concepts.QueryComplexity.Reflections
