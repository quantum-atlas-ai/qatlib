/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open Complex Metric Set
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_two_simple_poles {F : ℂ → E} {c a b : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c R))
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) (hab : a ≠ b) :
    (∮ z in C(c, R), ((z - a) * (z - b))⁻¹ • F z) =
      ((2 * Real.pi * I : ℂ) / (a - b)) • (F a - F b) := by
  have hR : 0 ≤ R := (dist_nonneg.trans_lt ha).le
  have hne (w : ℂ) (hw : w ∈ ball c R) :
      ∀ z ∈ sphere c R, z ≠ w :=
    fun z hz => ne_of_mem_of_not_mem hz (ne_of_lt hw)
  have hci (w : ℂ) (hw : w ∈ ball c R) :
      CircleIntegrable (fun z => (z - w)⁻¹ • F z) c R := by
    have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c R) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun z hz => sub_ne_zero.mpr (hne w hw z hz))
    exact (hinv.smul (hF.continuousOn_ball.mono sphere_subset_closedBall)).circleIntegrable hR
  have hparts : EqOn (fun z => ((z - a) * (z - b))⁻¹ • F z)
      (fun z => (a - b)⁻¹ • ((z - a)⁻¹ • F z - (z - b)⁻¹ • F z))
      (sphere c R) := by
    intro z hz
    dsimp only
    rw [← sub_smul, smul_smul]
    congr 1
    have hza : z - a ≠ 0 := sub_ne_zero.mpr (hne a ha z hz)
    have hzb : z - b ≠ 0 := sub_ne_zero.mpr (hne b hb z hz)
    have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    field_simp
    ring
  rw [circleIntegral.integral_congr hR hparts, circleIntegral.integral_smul,
    circleIntegral.integral_sub (hci a ha) (hci b hb),
    hF.circleIntegral_sub_inv_smul ha, hF.circleIntegral_sub_inv_smul hb,
    ← smul_sub, smul_smul]
  congr 1
  ring

theorem cbmd_linear_regulator_circle {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c R))
    (hi : I ∈ ball c R) (hzero : (0 : ℂ) ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (I / ((z - I) * z)) • F z) = F I - F 0 := by
  have htwo := circleIntegral_two_simple_poles hF hi hzero I_ne_zero
  have heq : (fun z => (I / ((z - I) * z)) • F z) =
      (fun z => I • (((z - I) * (z - 0))⁻¹ • F z)) := by
    funext z
    simp only [sub_zero, div_eq_mul_inv, smul_smul]
  rw [heq, circleIntegral.integral_smul, htwo, smul_smul, smul_smul]
  have hscalar : (2 * Real.pi * I : ℂ)⁻¹ *
      I * ((2 * Real.pi * I : ℂ) / (I - 0)) = 1 := by
    simp only [sub_zero]
    field_simp
  rw [hscalar, one_smul]

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
