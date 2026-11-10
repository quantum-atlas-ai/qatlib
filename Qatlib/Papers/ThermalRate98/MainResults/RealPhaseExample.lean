/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.MeasurementBorn
import Qatlib.Papers.ThermalRate98.MainResults.EvolutionInit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
variable {I : Type} [Fintype I] [DecidableEq I]

theorem diagonal_mulVec (d : I → ℂ) (v : QState I) :
    Matrix.diagonal d *ᵥ v = fun i => d i * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [if_neg (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem diagonal_mulVec_apply (d : I → ℂ) (v : QState I) (i : I) :
    (Matrix.diagonal d *ᵥ v) i = d i * v i := by
  rw [diagonal_mulVec]

theorem physicalPropagation_pauliZ_pi_quarter :
    physicalPropagation (Real.pi / 4) 1 PauliZ =
      Matrix.diagonal (fun b : Bool =>
        Complex.exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) *
          ((if b then (-1 : ℝ) else 1) : ℂ))) := by
  have hV : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ :=
    Submonoid.one_mem _
  have hH : PauliZ = (1 : Matrix Bool Bool ℂ) *
      Matrix.diagonal (fun b : Bool => ((if b then (-1 : ℝ) else 1) : ℂ)) *
      (1 : Matrix Bool Bool ℂ)ᴴ := by
    simp [PauliZ]
  rw [physicalPropagation,
    physical_scaled_exp (-Complex.I * (((Real.pi / 4) / 1 : ℝ) : ℂ)) PauliZ 1
      (fun b : Bool => if b then (-1 : ℝ) else 1) hV hH]
  simp

theorem uniform_bool_real (b : Bool) : (Uniform Bool b).im = 0 := by
  simp [Uniform]

theorem real_initial_can_become_complex :
    (((physicalPropagation (Real.pi / 4) 1 PauliZ) *ᵥ Uniform Bool) false).im = -1 / 2 := by
  rw [physicalPropagation_pauliZ_pi_quarter, diagonal_mulVec_apply]
  have hunif : Uniform Bool false = ((Real.sqrt 2 : ℂ))⁻¹ := by
    simp [Uniform]
  rw [hunif]

  have hexp : Complex.exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) *
      ((if (false : Bool) then (-1 : ℝ) else 1) : ℂ)) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [Bool.false_eq_true, if_false, Complex.ofReal_one, mul_one]
    rw [show -Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = (-(Real.pi / 4)) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I]
    have harg : (-(↑Real.pi / 4 : ℂ)) = ↑(-(Real.pi / 4)) := by push_cast; ring
    rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    ring

  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast hpos.ne'
  have hval : Complex.exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) *
      ((if (false : Bool) then (-1 : ℝ) else 1) : ℂ)) * ((Real.sqrt 2 : ℂ))⁻¹ =
      1 / 2 - (1 / 2 : ℂ) * Complex.I := by
    rw [hexp]
    field_simp [hne]
    have ha : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * 2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
      push_cast; ring
    linear_combination (1 - Complex.I) * ha
  rw [hval]
  norm_num

end Qatlib.Papers.ThermalRate98.MainResults
