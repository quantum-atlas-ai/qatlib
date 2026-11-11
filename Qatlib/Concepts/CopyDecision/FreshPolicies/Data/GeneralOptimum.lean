/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.FiniteEmbedding

/-!
# General Optimum

Fresh Policies constructions for Copy Decision.
Defines `generalPolicyRisks`, `generalPolicyOptimum`.
Proves `finiteRisks_subset_general`, `generalPolicyRisks_nonempty`, `generalPolicyRisks_bddBelow`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition

/-- Risk range of the explicitly defined risk-measurable relaxation, NOT a new
definition of the original physical causal-protocol class. -/
def generalPolicyRisks (n : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  Set.range (fun P : GeneralPolicy.{0} n => generalPolicyError P.program q)

/-- Definition of general Policy Optimum in the Fresh Policies construction. -/
def generalPolicyOptimum (n : ℕ) (q : Fin 3 → ℝ) : ℝ := sInf (generalPolicyRisks n q)

/-- The stated copy-decision construction satisfies `finiteRisks_subset_general` with the complete displayed premises. -/
lemma finiteRisks_subset_general (n : ℕ) (q : Fin 3 → ℝ) :
    finitePOVMRisks n q ⊆ generalPolicyRisks n q := by
  rintro _ ⟨F, rfl⟩
  exact ⟨F.asGeneral, F.toGeneral_error q⟩

/-- The stated copy-decision construction satisfies `generalPolicyRisks_nonempty` with the complete displayed premises. -/
lemma generalPolicyRisks_nonempty (n : ℕ) (q : Fin 3 → ℝ) :
    (generalPolicyRisks n q).Nonempty :=
  (finitePOVMRisks_nonempty n q).mono (finiteRisks_subset_general n q)

/-- The stated copy-decision construction satisfies `generalPolicyRisks_bddBelow` with the complete displayed premises. -/
lemma generalPolicyRisks_bddBelow (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    BddBelow (generalPolicyRisks n q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨P, rfl⟩
  exact generalPolicyError_nonneg P.program P.valid q hq

/-- The stated copy-decision construction satisfies `finitePOVMOptimum_le_generalError` with the complete displayed premises. -/
lemma finitePOVMOptimum_le_generalError {n : ℕ} (P : RawGeneralPolicy n)
    (hP : GeneralPolicyValid P) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    finitePOVMOptimum n q ≤ generalPolicyError P q := by
  by_contra h
  have hgap : 0 < finitePOVMOptimum n q-generalPolicyError P q := sub_pos.mpr (lt_of_not_ge h)
  have hQ : 0 ≤ ∑ i, q i := Finset.sum_nonneg (fun i _ => hq i)
  let ε : ℝ := (finitePOVMOptimum n q-generalPolicyError P q)/(2*((∑ i, q i)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨F, hF⟩ := generalPolicy_finite_approximation P hP q hq ε hε
  have hlo : finitePOVMOptimum n q ≤ povmPolicyError F q :=
    csInf_le (finitePOVMRisks_bddBelow n q hq) ⟨F, rfl⟩
  have hu := (abs_le.1 hF).2
  have he : ε*(2*((∑ i, q i)+1))=finitePOVMOptimum n q-generalPolicyError P q := by
    dsimp only [ε]
    exact div_mul_cancel₀ _ (by positivity : (2:ℝ)*((∑ i, q i)+1) ≠ 0)
  nlinarith only [hε, hlo, hu, he, hQ]

/-- Exact risk-infimum equality, with actual nonempty witnesses and lower
boundedness, despite the possible extra non-kernel-measurable relaxed trees. -/
theorem generalPolicyOptimum_eq_finite (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    generalPolicyOptimum n q=finitePOVMOptimum n q := by
  apply le_antisymm
  · exact csInf_le_csInf (generalPolicyRisks_bddBelow n q hq)
      (finitePOVMRisks_nonempty n q) (finiteRisks_subset_general n q)
  · apply le_csInf (generalPolicyRisks_nonempty n q)
    rintro _ ⟨P, rfl⟩
    exact finitePOVMOptimum_le_generalError P.program P.valid q hq

/-- The stated copy-decision construction satisfies `generalPolicyOptimum_uniform_lower` with the complete displayed premises. -/
theorem generalPolicyOptimum_uniform_lower (n : ℕ) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ generalPolicyOptimum (n+1) (fun _ => 1/3) := by
  rw [generalPolicyOptimum_eq_finite _ _ (by intro i; norm_num)]
  exact finitePOVMOptimum_uniform_lower n

/-- Integration contract for the ORIGINAL physical risk set. This theorem
requires actual class embeddings, not an assumed optimum or lower bound. -/
theorem physicalRiskSet_optimum {n : ℕ} (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (S : Set ℝ) (hfinite : finitePOVMRisks n q ⊆ S) (hgeneral : S ⊆ generalPolicyRisks n q) :
    sInf S=finitePOVMOptimum n q := by
  have hS : S.Nonempty := (finitePOVMRisks_nonempty n q).mono hfinite
  have hb : BddBelow S := (generalPolicyRisks_bddBelow n q hq).mono hgeneral
  apply le_antisymm
  · exact csInf_le_csInf hb (finitePOVMRisks_nonempty n q) hfinite
  · rw [← generalPolicyOptimum_eq_finite n q hq]
    exact csInf_le_csInf (generalPolicyRisks_bddBelow n q hq) hS hgeneral

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
