/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectiveWitness

/-!
# Collective Optimum

Collective Risk constructions for Copy Decision.
Defines `jointPOVMKraus`, `jointMeasurement`, `constantJointPOVM`.
Proves `full_matrix_inner`, `jointPOVMKraus_gram`, `jointPOVMKraus_mass`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError
open Matrix
open scoped ComplexOrder
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Definition of joint POVMKraus in the Collective Risk construction. -/
def jointPOVMKraus (Λ : POVM (Fin 3) α) (a : Fin 3) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α :=
  (Λ.mats a ^ (1/2:ℝ)).mat.toEuclideanLin

/-- The stated copy-decision construction satisfies `full_matrix_inner` with the complete displayed premises. -/
private lemma full_matrix_inner (A : Matrix α α ℂ) (x y : EuclideanSpace ℂ α) :
    inner ℂ (A.toEuclideanLin x) (A.toEuclideanLin y)=
      inner ℂ x ((A.conjTranspose*A).toEuclideanLin y) := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  change WithLp.toLp 2 (A.conjTranspose *ᵥ (A *ᵥ WithLp.ofLp y))=
    WithLp.toLp 2 ((A.conjTranspose*A) *ᵥ WithLp.ofLp y)
  rw [Matrix.mulVec_mulVec]

/-- The stated copy-decision construction satisfies `jointPOVMKraus_gram` with the complete displayed premises. -/
lemma jointPOVMKraus_gram (Λ : POVM (Fin 3) α) (x y : EuclideanSpace ℂ α) :
    ∑ a, inner ℂ (jointPOVMKraus Λ a x) (jointPOVMKraus Λ a y)=inner ℂ x y := by
  simp only [jointPOVMKraus, full_matrix_inner]
  have hm (a : Fin 3) : (Λ.mats a ^ (1/2:ℝ)).mat.conjTranspose*
      (Λ.mats a ^ (1/2:ℝ)).mat=(Λ.mats a).mat := by
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg a)]
  simp_rw [hm]
  have h := congrArg (fun A : HermitianMat α ℂ => inner ℂ x (A.mat.toEuclideanLin y))
    Λ.normalized
  simpa [map_sum, LinearMap.sum_apply, inner_sum, Matrix.toLpLin_apply] using h

/-- The stated copy-decision construction satisfies `jointPOVMKraus_mass` with the complete displayed premises. -/
lemma jointPOVMKraus_mass (Λ : POVM (Fin 3) α) (x : EuclideanSpace ℂ α) :
    ∑ a, ‖jointPOVMKraus Λ a x‖^2=‖x‖^2 := by
  have h := jointPOVMKraus_gram Λ x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The stated copy-decision construction satisfies `jointPOVMKraus_born` with the complete displayed premises. -/
lemma jointPOVMKraus_born (Λ : POVM (Fin 3) α) (a : Fin 3) (x : EuclideanSpace ℂ α) :
    ‖jointPOVMKraus Λ a x‖^2=jointBorn (Λ.mats a) x := by
  have h := full_matrix_inner (Λ.mats a ^ (1/2:ℝ)).mat x x
  rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg a)] at h
  calc
    _ = (inner ℂ (jointPOVMKraus Λ a x) (jointPOVMKraus Λ a x)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (jointPOVMKraus Λ a x)).symm
    _ = jointBorn (Λ.mats a) x := congrArg Complex.re h

/-- Definition of joint Measurement in the Collective Risk construction. -/
def jointMeasurement (Λ : POVM (Fin 3) α) :
    KrausMeasurement (EuclideanSpace ℂ α) (EuclideanSpace ℂ α) where
  op := jointPOVMKraus Λ
  mass_complete := jointPOVMKraus_mass Λ
  gram_complete := jointPOVMKraus_gram Λ

/-- The stated copy-decision construction satisfies `jointError_eq_decisionError` with the complete displayed premises. -/
lemma jointError_eq_decisionError {N : ℕ} (Λ : POVM (Fin 3) (Fin N → Fin 2))
    (q : Fin 3 → ℝ) :
    jointError Λ q=decisionError (fun a i => jointPOVMKraus Λ a (copyState N (trineState i))) q := by
  have hm (i : Fin 3) := jointPOVMKraus_mass Λ (copyState N (trineState i))
  simp only [trine_copies_unit, one_pow, Fin.sum_univ_three] at hm
  simp only [jointError, Fin.sum_univ_three, ← jointPOVMKraus_born, decisionError]
  linear_combination -(q 0)*(hm 0)-(q 1)*(hm 1)-(q 2)*(hm 2)

/-- The stated copy-decision construction satisfies `jointError_nonneg` with the complete displayed premises. -/
lemma jointError_nonneg {N : ℕ} (Λ : POVM (Fin 3) (Fin N → Fin 2))
    (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) : 0 ≤ jointError Λ q := by
  rw [jointError_eq_decisionError]
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  unfold decisionError
  positivity

/-- Universal lower bound for all complete collective decision POVMs on the
same full tensor register. No optimal measurement or finite-N PGM assumption. -/
theorem jointPOVM_uniform_lower {N : ℕ} (Λ : POVM (Fin 3) (Fin N → Fin 2)) :
    (1/4:ℝ)^N/(2*(1+(1/2:ℝ)^N)) ≤ jointError Λ (fun _ => 1/3) := by
  have h := kraus_error_bound (jointMeasurement Λ) (fun i => copyState N (trineState i))
    (fun _ => (1/3:ℝ)) (by intro i; norm_num) (by positivity : 0 ≤ (1/2:ℝ)^N)
    (trine_copies_unit N) (trine_copies_overlap N)
  norm_num [pairWeight] at h
  have he : ((1/2:ℝ)^N)^2=(1/4:ℝ)^N := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul]
    norm_num
  rw [he] at h
  rw [jointError_eq_decisionError]
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+(1/2:ℝ)^N))).2
  change (1/4:ℝ)^N*(1/2) ≤ (1+(1/2:ℝ)^N)*
    decisionError (fun a i => jointPOVMKraus Λ a (copyState N (trineState i))) _ at h
  nlinarith only [h]

/-- Definition of constant Joint POVM in the Collective Risk construction. -/
def constantJointPOVM : POVM (Fin 3) α where
  mats i := if i=0 then 1 else 0
  nonneg := by
    intro a
    split_ifs
    · exact HermitianMat.zero_le_iff.2 Matrix.PosSemidef.one
    · exact le_rfl
  normalized := by
    change (∑ i : Fin 3, if i=0 then (1:HermitianMat α ℂ) else 0)=1
    simp

/-- All three-decision joint POVMs, with effects on the entire tensor space. -/
def collectiveRisks (N : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  Set.range (fun Λ : POVM (Fin 3) (Fin N → Fin 2) => jointError Λ q)

/-- Definition of collective Optimum in the Collective Risk construction. -/
def collectiveOptimum (N : ℕ) (q : Fin 3 → ℝ) : ℝ := sInf (collectiveRisks N q)

/-- The stated copy-decision construction satisfies `collectiveRisks_nonempty` with the complete displayed premises. -/
lemma collectiveRisks_nonempty (N : ℕ) (q : Fin 3 → ℝ) : (collectiveRisks N q).Nonempty :=
  ⟨jointError constantJointPOVM q, ⟨constantJointPOVM, rfl⟩⟩

/-- The stated copy-decision construction satisfies `collectiveRisks_bddBelow` with the complete displayed premises. -/
lemma collectiveRisks_bddBelow (N : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    BddBelow (collectiveRisks N q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Λ, rfl⟩
  exact jointError_nonneg Λ q hq

/-- The stated copy-decision construction satisfies `collectiveOptimum_uniform_lower` with the complete displayed premises. -/
theorem collectiveOptimum_uniform_lower (N : ℕ) :
    (1/4:ℝ)^N/(2*(1+(1/2:ℝ)^N)) ≤ collectiveOptimum N (fun _ => 1/3) := by
  apply le_csInf (collectiveRisks_nonempty _ _)
  rintro _ ⟨Λ, rfl⟩
  exact jointPOVM_uniform_lower Λ

/-- The stated copy-decision construction satisfies `collectiveOptimum_uniform_upper` with the complete displayed premises. -/
theorem collectiveOptimum_uniform_upper (n : ℕ) :
    collectiveOptimum (n+2) (fun _ => 1/3) ≤
      2*(trineSignedOverlap (n+2))^2/
        (Real.sqrt (1+2*trineSignedOverlap (n+2))+Real.sqrt (1-trineSignedOverlap (n+2)))^2 := by
  rw [← trineCollectivePOVM_error_rational]
  exact csInf_le (collectiveRisks_bddBelow _ _ (by intro i; norm_num)) ⟨trineCollectivePOVM n, rfl⟩

end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
