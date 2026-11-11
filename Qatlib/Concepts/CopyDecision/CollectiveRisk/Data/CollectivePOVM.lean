/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectiveGeometry
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.POVMPolicy

/-!
# Collective POVM

Collective Risk constructions for Copy Decision.
Defines `fullPureMatrix`, `fullPureEffect`, `jointBorn`.
Proves `fullPureMatrix_hermitian`, `fullPureMatrix_action`, `fullPureMatrix_product`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError
open Matrix
open scoped ComplexOrder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Definition of full Pure Matrix in the Collective Risk construction. -/
def fullPureMatrix (u : EuclideanSpace ℂ α) : Matrix α α ℂ :=
  fun r c => u r*star (u c)

omit [Fintype α] [DecidableEq α] in
/-- The stated copy-decision construction satisfies `fullPureMatrix_hermitian` with the complete displayed premises. -/
lemma fullPureMatrix_hermitian (u : EuclideanSpace ℂ α) : (fullPureMatrix u).IsHermitian := by
  ext r c
  simp only [fullPureMatrix, Matrix.conjTranspose_apply, star_mul, star_star]

/-- The stated copy-decision construction satisfies `fullPureMatrix_action` with the complete displayed premises. -/
lemma fullPureMatrix_action (u x : EuclideanSpace ℂ α) :
    (fullPureMatrix u).toEuclideanLin x=(inner ℂ u x) • u := by
  ext r
  change (∑ c, u r*star (u c)*x c)=(∑ c, x c*star (u c))*u r
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [DecidableEq α] in
/-- The stated copy-decision construction satisfies `fullPureMatrix_product` with the complete displayed premises. -/
lemma fullPureMatrix_product (u v : EuclideanSpace ℂ α) :
    fullPureMatrix u*fullPureMatrix v=
      inner ℂ u v • (fun r c => u r*star (v c) : Matrix α α ℂ) := by
  ext r c
  change (∑ k, (u r*star (u k))*(v k*star (v c)))=
    (∑ k, v k*star (u k))*(u r*star (v c))
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq α] in
/-- The stated copy-decision construction satisfies `fullPureMatrix_idempotent` with the complete displayed premises. -/
lemma fullPureMatrix_idempotent (u : EuclideanSpace ℂ α) (hu : inner ℂ u u=1) :
    fullPureMatrix u*fullPureMatrix u=fullPureMatrix u := by
  rw [fullPureMatrix_product, hu, one_smul]
  rfl

omit [DecidableEq α] in
/-- The stated copy-decision construction satisfies `fullPureMatrix_mul_zero` with the complete displayed premises. -/
lemma fullPureMatrix_mul_zero (u v : EuclideanSpace ℂ α) (huv : inner ℂ u v=0) :
    fullPureMatrix u*fullPureMatrix v=0 := by
  rw [fullPureMatrix_product, huv, zero_smul]
  rfl

omit [DecidableEq α] in
/-- The stated copy-decision construction satisfies `projectionMatrix_nonneg` with the complete displayed premises. -/
lemma projectionMatrix_nonneg (A : Matrix α α ℂ) (hH : A.IsHermitian) (hA : A*A=A) :
    A.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [hH.eq, hA] at h

/-- Definition of full Pure Effect in the Collective Risk construction. -/
def fullPureEffect (u : EuclideanSpace ℂ α) : HermitianMat α ℂ :=
  ⟨fullPureMatrix u, fullPureMatrix_hermitian u⟩

/-- Born mass on the original full register, before any square-root realization. -/
def jointBorn (E : HermitianMat α ℂ) (x : EuclideanSpace ℂ α) : ℝ :=
  (inner ℂ x (E.mat.toEuclideanLin x)).re

/-- The stated copy-decision construction satisfies `jointBorn_pure` with the complete displayed premises. -/
lemma jointBorn_pure (u x : EuclideanSpace ℂ α) (r : ℝ)
    (h : inner ℂ u x=(r:ℂ)) : jointBorn (fullPureEffect u) x=r^2 := by
  change (inner ℂ x ((fullPureMatrix u).toEuclideanLin x)).re=_
  rw [fullPureMatrix_action, inner_smul_right, h, ← inner_conj_symm x u, h]
  norm_num
  ring

/-- Definition of orthogonal Pair POVM in the Collective Risk construction. -/
def orthogonalPairPOVM (u v : EuclideanSpace ℂ α)
    (hu : inner ℂ u u=1) (hv : inner ℂ v v=1) (huv : inner ℂ u v=0) :
    POVM (Fin 3) α where
  mats i := if i=0 then 1-fullPureEffect u-fullPureEffect v
    else if i=1 then fullPureEffect u else fullPureEffect v
  nonneg := by
    intro i
    have hP := fullPureMatrix_idempotent u hu
    have hQ := fullPureMatrix_idempotent v hv
    have hPQ := fullPureMatrix_mul_zero u v huv
    have hQP := fullPureMatrix_mul_zero v u (by rw [← inner_conj_symm, huv]; simp)
    have hH : ((1:Matrix α α ℂ)-fullPureMatrix u-fullPureMatrix v).IsHermitian :=
      (Matrix.isHermitian_one.sub (fullPureMatrix_hermitian u)).sub (fullPureMatrix_hermitian v)
    have hR : ((1:Matrix α α ℂ)-fullPureMatrix u-fullPureMatrix v)*
        (1-fullPureMatrix u-fullPureMatrix v)=1-fullPureMatrix u-fullPureMatrix v := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hP, hQ, hPQ, hQP]
      abel
    split_ifs
    · exact HermitianMat.zero_le_iff.2 (projectionMatrix_nonneg _ hH hR)
    · exact HermitianMat.zero_le_iff.2 (projectionMatrix_nonneg _ (fullPureMatrix_hermitian u) hP)
    · exact HermitianMat.zero_le_iff.2 (projectionMatrix_nonneg _ (fullPureMatrix_hermitian v) hQ)
  normalized := by
    simp only [Fin.sum_univ_three]
    norm_num [Fin.ext_iff]
    abel

/-- The stated copy-decision construction satisfies `jointBorn_complement` with the complete displayed premises. -/
lemma jointBorn_complement (u v x : EuclideanSpace ℂ α) :
    jointBorn (1-fullPureEffect u-fullPureEffect v) x=
      ‖x‖^2-jointBorn (fullPureEffect u) x-jointBorn (fullPureEffect v) x := by
  simp [jointBorn, map_sub, LinearMap.sub_apply, Matrix.toLpLin_one,
    inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Definition of joint Error in the Collective Risk construction. -/
def jointError {n : ℕ} (Λ : POVM (Fin 3) (Fin n → Fin 2)) (q : Fin 3 → ℝ) : ℝ :=
  ∑ i, q i*(1-jointBorn (Λ.mats i) (copyState n (trineState i)))

end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
