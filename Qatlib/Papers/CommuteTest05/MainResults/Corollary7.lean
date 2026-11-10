/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Operator BigOperators

namespace Qatlib.Papers.CommuteTest05.MainResults.Corollary7

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tailFunctional (s : ι → ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun M := s ⬝ᵥ (M *ᵥ fun _ => 1)
  map_add' M N := by
    simp only [add_mulVec, dotProduct_add]
  map_smul' a M := by
    simp only [smul_mulVec, dotProduct_smul, smul_eq_mul,
      RingHom.id_apply]

def expectedHittingTime (s : ι → ℝ) (A : Matrix ι ι ℝ) : ℝ :=
  ∑' t : ℕ, s ⬝ᵥ ((A ^ t) *ᵥ fun _ => 1)

theorem corollary7a_hitting_time
    (A : Matrix ι ι ℝ) (s : ι → ℝ) (hA : ‖A‖ < 1) :
    expectedHittingTime s A =
      s ⬝ᵥ ((1 - A)⁻¹ *ᵥ fun _ => 1) := by
  have hgeom : HasSum (fun t : ℕ => A ^ t) (Ring.inverse (1 - A)) :=
    hasSum_geom_series_inverse A hA
  have hmap : HasSum (fun t : ℕ => tailFunctional s (A ^ t))
      (tailFunctional s (Ring.inverse (1 - A))) :=
    (LinearMap.toContinuousLinearMap (tailFunctional s)).hasSum hgeom
  have hmap' : HasSum (fun t : ℕ => s ⬝ᵥ ((A ^ t) *ᵥ fun _ => 1))
      (s ⬝ᵥ ((1 - A)⁻¹ *ᵥ fun _ => 1)) := by
    simpa only [tailFunctional, LinearMap.coe_toContinuousLinearMap',
      Matrix.nonsing_inv_eq_ringInverse] using! hmap
  simpa only [expectedHittingTime, tailFunctional] using hmap'.tsum_eq

theorem corollary7b_spectral_hitting_time
    (A : Matrix ι ι ℝ) (hA : ‖A‖ < 1) (lam ν : ι → ℝ) (v : ι → ι → ℝ)
    (heig : ∀ i, A *ᵥ v i = lam i • v i)
    (horth : ∀ i j, (∑ x, v i x * v j x) = if i = j then 1 else 0)
    (hspan : (fun _ => 1 / Real.sqrt (Fintype.card ι)) = ∑ i, ν i • v i)
    (hcard : 0 < Fintype.card ι) :
    expectedHittingTime (fun _ => 1 / Fintype.card ι) A =
      ∑ i, ν i ^ 2 / (1 - lam i) := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast hcard
  have hsqrtpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqrtne : Real.sqrt N ≠ 0 := hsqrtpos.ne'
  rw [corollary7a_hitting_time A (fun _ => 1 / (Fintype.card ι : ℝ)) hA]
  set M : Matrix ι ι ℝ := 1 - A with hM
  have hunitM : IsUnit M := isUnit_one_sub_of_norm_lt_one hA
  have hunitdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM

  have hMv : ∀ i, M *ᵥ v i = (1 - lam i) • v i := by
    intro i
    rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec, heig i, sub_smul, one_smul]
  have hvnz : ∀ i, ‖v i‖ ≠ 0 := by
    intro i hzero
    have hv0 : v i = 0 := norm_eq_zero.mp hzero
    have hsum : (∑ x, v i x * v i x) = 1 := by simpa using horth i i
    rw [hv0] at hsum
    simp at hsum
  have habs : ∀ i, |lam i| ≤ ‖A‖ := by
    intro i
    have h := Matrix.linfty_opNorm_mulVec A (v i)
    rw [heig i, norm_smul, Real.norm_eq_abs] at h
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hvnz i)))
  have hlam_ne : ∀ i, lam i ≠ 1 := by
    intro i h
    have hlt : |lam i| < 1 := lt_of_le_of_lt (habs i) hA
    rw [h] at hlt
    norm_num at hlt
  have hinv : ∀ i, M⁻¹ *ᵥ v i = (1 - lam i)⁻¹ • v i := by
    intro i
    have hleft : M⁻¹ *ᵥ (M *ᵥ v i) = v i := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunitdet, Matrix.one_mulVec]
    rw [hMv i, Matrix.mulVec_smul] at hleft
    have hne : (1 - lam i) ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => hlam_ne i h.symm
    calc M⁻¹ *ᵥ v i = (1 - lam i)⁻¹ • ((1 - lam i) • (M⁻¹ *ᵥ v i)) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (1 - lam i)⁻¹ • v i := by rw [hleft]

  have hone : (fun _ : ι => (1 : ℝ)) = ∑ i, (Real.sqrt N * ν i) • v i := by
    have h1 : (fun _ : ι => (1 : ℝ)) =
        (Real.sqrt N) • (fun _ : ι => 1 / Real.sqrt N) := by
      ext x
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [h1, hspan, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _; rw [smul_smul]
  have hS : ∀ j, (∑ x, v j x) = Real.sqrt N * ν j := by
    intro j
    have hcongr := congrArg (fun w : ι → ℝ => ∑ x, v j x * w x) hspan
    change (∑ x, v j x * (1 / Real.sqrt N)) =
      (∑ x, v j x * ((∑ i, ν i • v i) : ι → ℝ) x) at hcongr
    have hL : (∑ x, v j x * (1 / Real.sqrt N)) =
        (∑ x, v j x) * (1 / Real.sqrt N) := by
      rw [Finset.sum_mul]
    have hR : (∑ x, v j x * ((∑ i, ν i • v i) : ι → ℝ) x) = ν j := by
      have hpoint : ∀ x, ((∑ i, ν i • v i) : ι → ℝ) x = ∑ i, ν i * v i x := by
        intro x; simp [Finset.sum_apply, smul_eq_mul]
      simp_rw [hpoint, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ i, (∑ x, v j x * (ν i * v i x)) =
          ν i * (∑ x, v j x * v i x) := by
        intro i; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      simp_rw [hinner, horth j]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    rw [hL, hR] at hcongr
    calc (∑ x, v j x) = ((∑ x, v j x) * (1 / Real.sqrt N)) * Real.sqrt N := by
            field_simp
      _ = ν j * Real.sqrt N := by rw [hcongr]
      _ = Real.sqrt N * ν j := by ring
  have hMinv_one : M⁻¹ *ᵥ (fun _ : ι => (1 : ℝ)) =
      ∑ i, (Real.sqrt N * ν i * (1 - lam i)⁻¹) • v i := by
    rw [hone, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_smul, hinv i, smul_smul]
  have hdot : (fun _ : ι => 1 / (Fintype.card ι : ℝ)) ⬝ᵥ
      (M⁻¹ *ᵥ fun _ => (1 : ℝ)) = ∑ i, ν i ^ 2 / (1 - lam i) := by
    rw [hMinv_one]
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ i, (∑ x, (1 / (Fintype.card ι : ℝ)) *
        ((Real.sqrt N * ν i * (1 - lam i)⁻¹) * v i x)) =
        ν i ^ 2 / (1 - lam i) := by
      intro i
      have hsumx : (∑ x, v i x) = Real.sqrt N * ν i := hS i
      rw [← Finset.mul_sum]
      have : (∑ x, (Real.sqrt N * ν i * (1 - lam i)⁻¹) * v i x) =
          (Real.sqrt N * ν i * (1 - lam i)⁻¹) * (∑ x, v i x) := by
        rw [Finset.mul_sum]
      rw [this, hsumx]
      have hsq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hNpos.le
      field_simp
      rw [hsq, ← hNdef]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  simpa [hM] using hdot

end Qatlib.Papers.CommuteTest05.MainResults.Corollary7
