/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section


/-!
# The affine origin criterion for a Gram matrix

This module proves the first equivalence in Lemma 4.6 of arXiv:2111.00405v1.
The witness is the normalized nonzero orthogonal residual of the all-ones vector
under the Moore-Penrose range projection of the Gram matrix.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder
open Matrix
open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46

/-- A matrix can be moved across the finite Hermitian inner product by taking its adjoint. -/
private theorem adjoint_dot {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ)
    (x : Fin n → ℂ) (y : Fin k → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  simp only [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

/-- The origin belongs to the affine image exactly when the Gram range misses the ones vector. -/
theorem affine_kernel {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ) :
    (∃ x : Fin k → ℂ, (∑ i, x i) = 1 ∧ V *ᵥ x = 0) ↔
      ¬ ∃ y : Fin k → ℂ, (Vᴴ * V) *ᵥ y = fun _ => 1 := by
  let G := Vᴴ * V
  let one : Fin k → ℂ := fun _ => 1
  constructor
  · rintro ⟨x, hxsum, hxzero⟩ ⟨y, hy⟩
    change G *ᵥ y = one at hy
    have hzero : star x ⬝ᵥ one = 0 := by
      rw [← hy]
      change star x ⬝ᵥ ((Vᴴ * V) *ᵥ y) = 0
      rw [← mulVec_mulVec, adjoint_dot]
      simp [hxzero]
    have hone : star x ⬝ᵥ one = 1 := by
      simp only [one, dotProduct, Pi.star_apply, mul_one]
      rw [← star_sum, hxsum, star_one]
    exact one_ne_zero (hone.symm.trans hzero)
  · intro hmiss
    let P := G * matrixPseudoinverse G
    let r := one - P *ᵥ one
    have hG : Gᴴ = G := by simp [G]
    have hP : Pᴴ = P := mul_matrixPseudoinverse_adjoint G
    have hPG : P * G = G := mul_matrixPseudoinverse_mul G
    have hGP : G * P = G := by
      have h := congrArg Matrix.conjTranspose hPG
      simpa only [conjTranspose_mul, hG, hP] using h
    have hPP : P * P = P := by
      change (G * matrixPseudoinverse G) * (G * matrixPseudoinverse G) = _
      rw [← Matrix.mul_assoc, mul_matrixPseudoinverse_mul]
    have hPr : P *ᵥ r = 0 := by
      dsimp only [r]
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPP, sub_self]
    have hGr : G *ᵥ r = 0 := by
      dsimp only [r]
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hGP, sub_self]
    have hr : r ≠ 0 := by
      intro hrzero
      apply hmiss
      refine ⟨matrixPseudoinverse G *ᵥ one, ?_⟩
      rw [Matrix.mulVec_mulVec]
      exact (sub_eq_zero.mp hrzero).symm
    have hcross : star r ⬝ᵥ (P *ᵥ one) = 0 := by
      rw [adjoint_dot, hP, hPr]
      simp
    have hsum : (∑ i, r i) ≠ 0 := by
      intro hsumzero
      apply hr
      apply dotProduct_star_self_eq_zero.mp
      have hsumone : star r ⬝ᵥ one = 0 := by
        simp only [one, dotProduct, Pi.star_apply, mul_one]
        rw [← star_sum, hsumzero, star_zero]
      calc
        star r ⬝ᵥ r = star r ⬝ᵥ one - star r ⬝ᵥ (P *ᵥ one) :=
          dotProduct_sub _ _ _
        _ = 0 := by rw [hsumone, hcross, sub_self]
    refine ⟨(∑ i, r i)⁻¹ • r, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hsum
    · rw [Matrix.mulVec_smul]
      have hVr : V *ᵥ r = 0 :=
        (Matrix.conjTranspose_mul_self_mulVec_eq_zero V r).mp hGr
      rw [hVr, smul_zero]

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
