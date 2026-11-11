/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.BinaryAdaptive
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.CausalPolicy

/-!
# Anti Trine Upper

Fresh Policies constructions for Copy Decision.
Defines `antiTrineMatrix`, `antiTrineEffect`, `antiTrinePOVM`.
Proves `trinePureMatrix_idempotent`, `antiTrineMatrix_hermitian`, `antiTrineMatrix_sum`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open Matrix
open scoped ComplexOrder

/-- The stated copy-decision construction satisfies `trinePureMatrix_idempotent` with the complete displayed premises. -/
lemma trinePureMatrix_idempotent (i : Fin 3) :
    trinePureMatrix i*trinePureMatrix i=trinePureMatrix i := by
  have hn : (∑ k, trineState i k*star (trineState i k))=1 := by
    change inner ℂ (trineState i) (trineState i)=1
    rw [trineState_gram, if_pos rfl]
  ext r c
  change (∑ k, (trineState i r*star (trineState i k))*(trineState i k*star (trineState i c)))=_
  calc
    _ = (trineState i r*star (trineState i c))*(∑ k, trineState i k*star (trineState i k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hn, mul_one]; rfl

/-- Definition of anti Trine Matrix in the Fresh Policies construction. -/
def antiTrineMatrix (i : Fin 3) : QubitMatrix := (2/3:ℂ) • (1-trinePureMatrix i)

/-- The stated copy-decision construction satisfies `antiTrineMatrix_hermitian` with the complete displayed premises. -/
lemma antiTrineMatrix_hermitian (i : Fin 3) : (antiTrineMatrix i).IsHermitian := by
  change (antiTrineMatrix i).conjTranspose=_
  simp [antiTrineMatrix, Matrix.conjTranspose_smul, (trinePureMatrix_hermitian i).eq]

/-- Definition of anti Trine Effect in the Fresh Policies construction. -/
def antiTrineEffect (i : Fin 3) : HermitianMat (Fin 2) ℂ :=
  ⟨antiTrineMatrix i, antiTrineMatrix_hermitian i⟩

/-- The stated copy-decision construction satisfies `antiTrineMatrix_sum` with the complete displayed premises. -/
lemma antiTrineMatrix_sum : ∑ i, antiTrineMatrix i=1 := by
  have he : trinePureMatrix 0+trinePureMatrix 1+trinePureMatrix 2=(3/2:ℂ) • (1:QubitMatrix) := by
    have h0 := (trinePureMatrix_explicit 0).trans (if_pos rfl)
    have h1 := ((trinePureMatrix_explicit 1).trans (if_neg (by decide))).trans (if_pos rfl)
    have h2 := ((trinePureMatrix_explicit 2).trans (if_neg (by decide))).trans (if_neg (by decide))
    rw [h0, h1, h2]
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [Matrix.one_apply]
    all_goals ring
  simp only [Fin.sum_univ_three, antiTrineMatrix]
  rw [← smul_add, ← smul_add]
  have hr : (1:QubitMatrix)-trinePureMatrix 0+(1-trinePureMatrix 1)+(1-trinePureMatrix 2)=
      (3:ℂ) • 1-(trinePureMatrix 0+trinePureMatrix 1+trinePureMatrix 2) := by module
  rw [hr, he]
  ext r c
  simp
  ring

/-- The complete anti-trine POVM on the actual qubit, including all inputs. -/
def antiTrinePOVM : POVM (Fin 3) (Fin 2) where
  mats := antiTrineEffect
  nonneg := by
    intro i
    apply HermitianMat.zero_le_iff.2
    have hP := trinePureMatrix_idempotent i
    have hH := (trinePureMatrix_hermitian i).eq
    have hm : ((1:QubitMatrix)-trinePureMatrix i)*(1-trinePureMatrix i)=1-trinePureMatrix i := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, hP, sub_self, sub_zero]
    have h := Matrix.posSemidef_conjTranspose_mul_self ((1:QubitMatrix)-trinePureMatrix i)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, hm] at h
    exact h.smul (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 2/3)
  normalized := by
    apply HermitianMat.ext
    exact antiTrineMatrix_sum

/-- The stated copy-decision construction satisfies `antiTrinePOVM_born` with the complete displayed premises. -/
theorem antiTrinePOVM_born (a i : Fin 3) :
    qubitBorn (antiTrinePOVM.mats a) (trineState i)=if a=i then 0 else (1/2:ℝ) := by
  change (inner ℂ (trineState i) ((antiTrineMatrix a).toEuclideanLin (trineState i))).re=_
  simp only [antiTrineMatrix, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply,
    Matrix.toLpLin_one, LinearMap.id_apply, inner_smul_right, inner_sub_right,
    trinePureMatrix_quadratic]
  by_cases h : a=i
  · norm_num [h, trineState_unit]
  · norm_num [h, trineState_unit]

/-- The stated copy-decision construction satisfies `antiTrine_branch_prior` with the complete displayed premises. -/
lemma antiTrine_branch_prior (a : Fin 3) :
    (fun i => (1/3:ℝ)*qubitBorn (antiTrinePOVM.mats a) (trineState i))=
      pairPrior (a+1) (a+2) (1/6) (1/6) := by
  funext i
  rw [antiTrinePOVM_born]
  fin_cases a <;> fin_cases i <;> norm_num [pairPrior, Fin.add_def, Fin.ext_iff]

/-- Definition of anti Trine Adaptive in the Fresh Policies construction. -/
def antiTrineAdaptive (n : ℕ) : FinitePOVMPolicy (n+1) :=
  .step 3 antiTrinePOVM (fun a => binaryAdaptive n (a+1) (a+2)
    (by fin_cases a <;> decide) (1/6) (1/6) (by norm_num) (by norm_num))

/-- Same physical first step and actual conditional binary continuations. -/
theorem antiTrineAdaptive_error (n : ℕ) :
    povmPolicyError (antiTrineAdaptive n) (fun _ => (1:ℝ)/3)=
      (1-Real.sqrt (1-(1/4:ℝ)^n))/2 := by
  unfold antiTrineAdaptive
  rw [povmPolicyError]
  simp_rw [antiTrine_branch_prior, binaryAdaptive_error]
  simp only [Fin.sum_univ_three]
  have he : ((1/6:ℝ)+1/6)^2-4*(1/6)*(1/6)*(1/4:ℝ)^n=(1/3:ℝ)^2*(1-(1/4:ℝ)^n) := by ring
  unfold binaryRisk
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/3)]
  ring

/-- The stated copy-decision construction satisfies `finitePOVMOptimum_uniform_upper` with the complete displayed premises. -/
theorem finitePOVMOptimum_uniform_upper (n : ℕ) :
    finitePOVMOptimum (n+1) (fun _ => (1:ℝ)/3) ≤ (1-Real.sqrt (1-(1/4:ℝ)^n))/2 := by
  rw [← antiTrineAdaptive_error]
  exact csInf_le (finitePOVMRisks_bddBelow _ _ (by intro i; norm_num)) ⟨antiTrineAdaptive n, rfl⟩

/-- The stated copy-decision construction satisfies `causalPolicyOptimum_uniform_upper` with the complete displayed premises. -/
theorem causalPolicyOptimum_uniform_upper (n : ℕ) :
    causalPolicyOptimum (n+1) (fun _ => (1:ℝ)/3) ≤ (1-Real.sqrt (1-(1/4:ℝ)^n))/2 := by
  rw [causalPolicyOptimum_eq_finite _ _ (by intro i; norm_num)]
  exact finitePOVMOptimum_uniform_upper n

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
