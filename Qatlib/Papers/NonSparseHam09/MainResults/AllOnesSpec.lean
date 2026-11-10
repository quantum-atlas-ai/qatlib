/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Thm3DenseLowerBound
import Qatlib.Papers.NonSparseHam09.MainResults.NormChain
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma const_one_mulVec (v : ι → ℂ) :
    (fun _ _ : ι => (1 : ℂ)) *ᵥ v = fun _ => ∑ j, v j := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem specNorm_const_one :
    specNorm (fun _ _ : ι => (1 : ℂ)) = (Fintype.card ι : ℝ) := by
  set J : Matrix ι ι ℂ := fun _ _ => (1 : ℂ) with hJ
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine le_antisymm ?_ ?_
  · rw [specNorm_eq_l2, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ hcard fun v => ?_
    have hdelC : (⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) J) v
        = (EuclideanSpace.equiv ι ℂ).symm (J *ᵥ v.ofLp) := by
      apply WithLp.ofLp_injective
      simp [Matrix.ofLp_toEuclideanCLM]
    rw [hdelC, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    rw [const_one_mulVec]
    change Real.sqrt (∑ i : ι, ‖∑ j, v.ofLp j‖ ^ 2)
        ≤ (Fintype.card ι : ℝ) * Real.sqrt (∑ i : ι, ‖v.ofLp i‖ ^ 2)

    have hsum : (∑ _i : ι, ‖∑ j, v.ofLp j‖ ^ 2)
        = (Fintype.card ι : ℝ) * ‖∑ j, v.ofLp j‖ ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    rw [hsum]

    have hcs : ‖∑ j, v.ofLp j‖ ^ 2
        ≤ (Fintype.card ι : ℝ) * (∑ j, ‖v.ofLp j‖ ^ 2) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun _ => (1 : ℝ)) (fun j => ‖v.ofLp j‖)
      have hcard' : (∑ i : ι, (1 : ℝ) ^ 2) = (Fintype.card ι : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ]
      rw [hcard'] at h
      have hnorm : ‖∑ j, v.ofLp j‖ ≤ ∑ j, ‖v.ofLp j‖ := norm_sum_le _ _
      have hnn : (0 : ℝ) ≤ ‖∑ j, v.ofLp j‖ := norm_nonneg _
      have hsq : ‖∑ j, v.ofLp j‖ ^ 2 ≤ (∑ j, ‖v.ofLp j‖) ^ 2 :=
        pow_le_pow_left₀ hnn hnorm 2
      exact hsq.trans (by simpa using h)
    have hsqrt : Real.sqrt ((Fintype.card ι : ℝ) * ‖∑ j, v.ofLp j‖ ^ 2)
        ≤ Real.sqrt ((Fintype.card ι : ℝ) ^ 2 * (∑ j, ‖v.ofLp j‖ ^ 2)) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [hcs, hcard]
    refine hsqrt.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg (Fintype.card ι : ℝ)), Real.sqrt_sq hcard]
  · have hmem := specNorm_mulVec J
        ((WithLp.toLp 2 (fun _ : ι => (1 : ℂ))) : EuclideanSpace ℂ ι)
    have hnorm : ‖(WithLp.toLp 2 (fun _ : ι => (1 : ℂ)) : EuclideanSpace ℂ ι)‖
        = Real.sqrt (Fintype.card ι : ℝ) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hnorm, WithLp.ofLp_toLp] at hmem
    have hmv : J *ᵥ (fun _ : ι => (1 : ℂ)) = fun _ => (Fintype.card ι : ℂ) := by
      rw [const_one_mulVec]
      funext i
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hmv] at hmem
    have hleft : ‖(EuclideanSpace.equiv ι ℂ).symm
        (fun _ => (Fintype.card ι : ℂ))‖
        = (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
      rw [EuclideanSpace.norm_eq]
      have hcoord : ∀ i : ι, ((EuclideanSpace.equiv ι ℂ).symm
          (fun _ => (Fintype.card ι : ℂ))).ofLp i = (Fintype.card ι : ℂ) := fun i => rfl
      have hsum2 : (∑ i : ι, ‖((EuclideanSpace.equiv ι ℂ).symm
          (fun _ => (Fintype.card ι : ℂ))).ofLp i‖ ^ 2)
          = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) ^ 2 := by
        simp only [hcoord]
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.norm_natCast]
      rw [hsum2, show (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) ^ 2
          = ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) ^ 2 by
        rw [mul_pow, Real.sq_sqrt hcard]; ring]
      exact Real.sqrt_sq (by positivity)
    rw [hleft] at hmem

    have hsqrtpos : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hpos
    exact le_of_mul_le_mul_right hmem hsqrtpos

end Qatlib.Papers.NonSparseHam09.MainResults
