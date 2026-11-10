/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import Mathlib.Tactic
set_option warningAsError false
set_option autoImplicit false
open Matrix
open scoped Classical
namespace Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram

abbrev MomentIndex (n : ℕ) := Fin n × Fin 2

noncomputable def factor {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) : Matrix (MomentIndex n) (MomentIndex n) ℝ :=
  (HermitianMat.sqrt (⟨Δ,hΔ.isHermitian⟩ : HermitianMat (MomentIndex n) ℝ)).mat

theorem factor_square {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef) :
    factor Δ hΔ * factor Δ hΔ = Δ :=
  HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hΔ)

theorem factor_symmetric {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef) :
    (factor Δ hΔ).transpose = factor Δ hΔ := by
  exact (HermitianMat.sqrt (⟨Δ,hΔ.isHermitian⟩ : HermitianMat (MomentIndex n) ℝ)).H

theorem row_gram {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef)
    (a b : MomentIndex n) : ∑ c, factor Δ hΔ a c * factor Δ hΔ b c = Δ a b := by
  have h : factor Δ hΔ * (factor Δ hΔ).transpose = Δ := by
    rw [factor_symmetric]
    exact factor_square Δ hΔ
  simpa only [Matrix.mul_apply,Matrix.transpose_apply] using congrArg (fun M => M a b) h

noncomputable def fitVector {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) (i : Fin n) : Fin 2 × MomentIndex n → ℝ :=
  fun c => (Real.sqrt 2)⁻¹ * factor Δ hΔ (i,c.1) c.2

theorem fit_dot {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef)
    (i j : Fin n) :
    ∑ c, fitVector Δ hΔ i c * fitVector Δ hΔ j c =
      (Δ (i,0) (j,0)+Δ (i,1) (j,1))/2 := by
  have hr : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹ = (1/2:ℝ) := by
    rw [← mul_inv,← sq,Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [fitVector]
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ (a b : ℝ), ((Real.sqrt 2)⁻¹*a)*((Real.sqrt 2)⁻¹*b)=(1/2)* (a*b)
    from fun a b => by calc _ = ((Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹)*(a*b) := by ring
                           _ = _ := by rw [hr]]
  simp_rw [← Finset.mul_sum,row_gram]
  rw [Fin.sum_univ_two]
  ring

theorem fit_unit {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef)
    (hdiag : ∀ a, Δ a a = 1) (i : Fin n) : ∑ c, (fitVector Δ hΔ i c)^2 = 1 := by
  have h := fit_dot Δ hΔ i i
  norm_num only [pow_two,hdiag] at h
  simpa only [pow_two] using h

theorem fit_correlation_range {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hΔ : Δ.PosSemidef)
    (hdiag : ∀ a, Δ a a = 1) (i j : Fin n) :
    -1 ≤ (Δ (i,0) (j,0)+Δ (i,1) (j,1))/2 ∧
      (Δ (i,0) (j,0)+Δ (i,1) (j,1))/2 ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fitVector Δ hΔ i) (fitVector Δ hΔ j)
  rw [fit_unit Δ hΔ hdiag i,fit_unit Δ hΔ hdiag j,fit_dot] at h
  constructor <;> nlinarith
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
