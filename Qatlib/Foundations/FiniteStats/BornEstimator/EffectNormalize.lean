/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Measurements.POVM
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {d V Ω : Type*} [Fintype d] [DecidableEq d] [Fintype V] [Fintype Ω]

omit [DecidableEq d] in

theorem effect_trace_pos (E : HermitianMat d ℂ) (hE : 0 ≤ E) (hne : E≠0) : 0<E.trace :=
  HermitianMat.trace_pos (lt_of_le_of_ne hE hne.symm)

def normalizedEffect (E : HermitianMat d ℂ) (hE : 0 ≤ E) (hne : E≠0) : MState d where
  M := E.trace⁻¹ • E
  nonneg := smul_nonneg (inv_nonneg.mpr (effect_trace_pos E hE hne).le) hE
  tr := by rw [HermitianMat.trace_smul,inv_mul_cancel₀ (effect_trace_pos E hE hne).ne']

theorem normalizedEffect_exp (E A : HermitianMat d ℂ) (hE : 0 ≤ E) (hne : E≠0) :
    (normalizedEffect E hE hne).exp_val A=⟪E,A⟫/E.trace := by
  change ⟪E.trace⁻¹ • E,A⟫=_
  rw [real_inner_smul_left]
  ring

theorem density_norm_le_one (ρ : MState d) : ‖ρ.M‖ ≤ 1 := by
  have h := HermitianMat.inner_le_mul_trace ρ.nonneg ρ.nonneg
  rw [ρ.tr,mul_one,real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg ρ.M]

theorem density_exp_abs_le_norm (ρ : MState d) (A : HermitianMat d ℂ) : |ρ.exp_val A| ≤ ‖A‖ :=
  (abs_real_inner_le_norm ρ.M A).trans ((mul_le_mul_of_nonneg_right (density_norm_le_one ρ) (norm_nonneg A)).trans_eq (one_mul _))

def quadraticScore (S : V → HermitianMat d ℂ) (w : V → ℝ) (ρ : MState d) : ℝ :=
  ∑ i,w i*(ρ.exp_val (S i))^2

theorem quadraticScore_le (S : V → HermitianMat d ℂ) (w : V → ℝ) (hw : ∀ i,0 ≤ w i) (ρ : MState d) :
    quadraticScore S w ρ ≤ ∑ i,w i*‖S i‖^2 := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  have h := density_exp_abs_le_norm ρ (S i)
  nlinarith [abs_nonneg (ρ.exp_val (S i)),sq_abs (ρ.exp_val (S i))]

end Qatlib.Foundations.FiniteStats.BornEstimator
