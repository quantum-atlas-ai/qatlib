/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.PartialFraction
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open Complex Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_finite_simple_poles {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hs : s.Nonempty) (hp : Set.InjOn p s)
    {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c R))
    (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    (∮ z in C(c, R), (∏ i ∈ s, (z - p i))⁻¹ • F z) =
      (2 * Real.pi * I : ℂ) •
        ∑ i ∈ s, (∏ j ∈ s.erase i, (p i - p j))⁻¹ • F (p i) := by
  obtain ⟨i₀, hi₀⟩ := hs
  have hR : 0 ≤ R := (dist_nonneg.trans_lt (hinside i₀ hi₀)).le
  have hne (i : ι) (hi : i ∈ s) : ∀ z ∈ sphere c R, z ≠ p i :=
    fun z hz => ne_of_mem_of_not_mem hz (ne_of_lt (hinside i hi))
  have hci (i : ι) (hi : i ∈ s) :
      CircleIntegrable (fun z => (z - p i)⁻¹ • F z) c R := by
    have hinv : ContinuousOn (fun z : ℂ => (z - p i)⁻¹) (sphere c R) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun z hz => sub_ne_zero.mpr (hne i hi z hz))
    exact (hinv.smul (hF.continuousOn_ball.mono sphere_subset_closedBall)).circleIntegrable hR
  have hparts : EqOn (fun z => (∏ i ∈ s, (z - p i))⁻¹ • F z)
      (fun z => ∑ i ∈ s,
        (∏ j ∈ s.erase i, (p i - p j))⁻¹ • ((z - p i)⁻¹ • F z))
      (sphere c R) := by
    intro z hz
    dsimp only
    rw [finite_simple_pole_partial_fraction s p ⟨i₀, hi₀⟩ hp z
      (fun i hi => hne i hi z hz), Finset.sum_smul]
    simp only [mul_smul]
  have hcis (i : ι) (hi : i ∈ s) :
      CircleIntegrable (fun z =>
        (∏ j ∈ s.erase i, (p i - p j))⁻¹ • ((z - p i)⁻¹ • F z)) c R :=
    (hci i hi).smul_of_continuousOn (g := fun _ : ℂ =>
      (∏ j ∈ s.erase i, (p i - p j))⁻¹) continuousOn_const
  rw [circleIntegral.integral_congr hR hparts,
    circleIntegral.integral_fun_sum hcis]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [circleIntegral.integral_smul,
    hF.circleIntegral_sub_inv_smul (hinside i hi), smul_comm]

theorem cbmd_finite_polynomial_regulator_circle {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hp : Set.InjOn p s)
    (i₀ : ι) (hi₀ : i₀ ∈ s)
    {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c R))
    (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (∏ j ∈ s.erase i₀, (p i₀ - p j)) •
          ((∏ i ∈ s, (z - p i))⁻¹ • F z)) =
      F (p i₀) + ∑ i ∈ s.erase i₀,
        ((∏ j ∈ s.erase i₀, (p i₀ - p j)) *
          (∏ j ∈ s.erase i, (p i - p j))⁻¹) • F (p i) := by
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hD : (∏ j ∈ s.erase i₀, (p i₀ - p j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro he
    exact (Finset.mem_erase.mp hj).1 (hp (Finset.mem_erase.mp hj).2 hi₀ he.symm)
  rw [circleIntegral.integral_smul,
    circleIntegral_finite_simple_poles s p ⟨i₀, hi₀⟩ hp hF hinside]
  rw [smul_comm (∏ j ∈ s.erase i₀, (p i₀ - p j)), inv_smul_smul₀ hC]
  rw [← Finset.add_sum_erase _ _ hi₀, smul_add, smul_smul,
    mul_inv_cancel₀ hD, one_smul, Finset.smul_sum]
  simp only [smul_smul]

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
