/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectiveApproximation
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.BinaryAdaptive
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# General Collective Optimum

Collective Risk constructions for Copy Decision.
Defines `GeneralJointPOVM.ofFinite`, `GeneralCollectivePolicy`, `GeneralCollectivePolicy.error`.
Proves `GeneralJointPOVM.ofFinite_born_singleton`, `GeneralJointPOVM.ofFinite_randomizedError`, `GeneralCollectivePolicy.ofFinite_error`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Definition of of Finite in the Collective Risk construction. -/
def GeneralJointPOVM.ofFinite {N m : ℕ} (Λ : POVM (Fin m) (Fin N → Fin 2)) :
    GeneralJointPOVM N (Fin m) where
  effects := ∑ a, VectorMeasure.dirac a (Λ.mats a)
  nonneg := by
    intro B hB
    simp only [VectorMeasure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_nonneg
    intro a _
    by_cases ha : a ∈ B
    · rw [VectorMeasure.dirac_apply_of_mem hB ha]
      exact Λ.nonneg a
    · rw [VectorMeasure.dirac_apply_of_notMem ha]
  normalized := by simpa using Λ.normalized

/-- The stated copy-decision construction satisfies `GeneralJointPOVM.ofFinite_born_singleton` with the complete displayed premises. -/
lemma GeneralJointPOVM.ofFinite_born_singleton {N m : ℕ}
    (Λ : POVM (Fin m) (Fin N → Fin 2)) (a : Fin m)
    (x : EuclideanSpace ℂ (Fin N → Fin 2)) :
    ((GeneralJointPOVM.ofFinite Λ).bornMeasure x).real {a}=jointBorn (Λ.mats a) x := by
  rw [GeneralJointPOVM.bornMeasure_real _ _ (measurableSet_singleton _)]
  congr 1
  simp [GeneralJointPOVM.ofFinite, VectorMeasure.dirac]

/-- The stated copy-decision construction satisfies `GeneralJointPOVM.ofFinite_randomizedError` with the complete displayed premises. -/
lemma GeneralJointPOVM.ofFinite_randomizedError {N m : ℕ}
    (Λ : POVM (Fin m) (Fin N → Fin 2)) (p : Fin m → TerminalDecision) (q : Fin 3 → ℝ) :
    (GeneralJointPOVM.ofFinite Λ).randomizedError p q=
      ∑ a, ∑ i, q i*jointBorn (Λ.mats a) (copyState N (trineState i))*(1-(p a).prob i) := by
  have hi (i : Fin 3) :
      (∫ a, (1-(p a).prob i) ∂(GeneralJointPOVM.ofFinite Λ).bornMeasure (copyState N (trineState i)))=
        ∑ a, jointBorn (Λ.mats a) (copyState N (trineState i))*(1-(p a).prob i) := by
    have hint := integrable_unitRisk
      ((GeneralJointPOVM.ofFinite Λ).bornMeasure (copyState N (trineState i)))
      (fun a => 1-(p a).prob i) (measurable_of_finite _)
      (fun a => ⟨sub_nonneg.2 (terminal_prob_le_one (p a) i), by linarith [(p a).nonneg i]⟩)
    rw [integral_fintype hint]
    simp only [GeneralJointPOVM.ofFinite_born_singleton, smul_eq_mul]
  unfold GeneralJointPOVM.randomizedError
  simp_rw [hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Complete arbitrary-outcome joint POVM plus a measurable randomized decoder.
The original full tensor register is the measurement input. -/
structure GeneralCollectivePolicy (N : ℕ) where
  Outcome : Type
  space : MeasurableSpace Outcome
  measurement : @GeneralJointPOVM N Outcome space
  guess : Outcome → TerminalDecision
  measurable_guess : ∀ i, @Measurable Outcome ℝ space inferInstance (fun y => (guess y).prob i)

/-- Definition of error in the Collective Risk construction. -/
def GeneralCollectivePolicy.error {N : ℕ} (P : GeneralCollectivePolicy N) (q : Fin 3 → ℝ) : ℝ :=
  @GeneralJointPOVM.randomizedError N P.Outcome P.space P.measurement P.guess q

/-- Definition of of Finite in the Collective Risk construction. -/
def GeneralCollectivePolicy.ofFinite {N : ℕ} (Λ : POVM (Fin 3) (Fin N → Fin 2)) :
    GeneralCollectivePolicy N where
  Outcome := Fin 3
  space := inferInstance
  measurement := GeneralJointPOVM.ofFinite Λ
  guess := guessDecision
  measurable_guess _ := measurable_of_finite _

/-- The stated copy-decision construction satisfies `GeneralCollectivePolicy.ofFinite_error` with the complete displayed premises. -/
lemma GeneralCollectivePolicy.ofFinite_error {N : ℕ} (Λ : POVM (Fin 3) (Fin N → Fin 2))
    (q : Fin 3 → ℝ) : (GeneralCollectivePolicy.ofFinite Λ).error q=jointError Λ q := by
  change (GeneralJointPOVM.ofFinite Λ).randomizedError guessDecision q=_
  rw [GeneralJointPOVM.ofFinite_randomizedError, ← finiteJointDecode_error]
  have he (i : Fin 3) : (finiteJointDecode Λ guessDecision).mats i=Λ.mats i := by
    change (∑ a, (guessDecision a).prob i • Λ.mats a)=Λ.mats i
    simp [guessDecision, eq_comm]
  unfold jointError
  simp_rw [he]

/-- The stated copy-decision construction satisfies `GeneralCollectivePolicy.error_nonneg` with the complete displayed premises. -/
lemma GeneralCollectivePolicy.error_nonneg {N : ℕ} (P : GeneralCollectivePolicy N)
    (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) : 0 ≤ P.error q := by
  letI := P.space
  unfold GeneralCollectivePolicy.error GeneralJointPOVM.randomizedError
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hq i)
  exact integral_nonneg (fun y => sub_nonneg.2 (terminal_prob_le_one (P.guess y) i))

/-- Definition of general Collective Risks in the Collective Risk construction. -/
def generalCollectiveRisks (N : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  Set.range (fun P : GeneralCollectivePolicy N => P.error q)

/-- Definition of general Collective Optimum in the Collective Risk construction. -/
def generalCollectiveOptimum (N : ℕ) (q : Fin 3 → ℝ) : ℝ := sInf (generalCollectiveRisks N q)

/-- The stated copy-decision construction satisfies `jointRisks_subset_general` with the complete displayed premises. -/
lemma jointRisks_subset_general (N : ℕ) (q : Fin 3 → ℝ) :
    collectiveRisks N q ⊆ generalCollectiveRisks N q := by
  rintro _ ⟨Λ, rfl⟩
  exact ⟨GeneralCollectivePolicy.ofFinite Λ, GeneralCollectivePolicy.ofFinite_error Λ q⟩

/-- The stated copy-decision construction satisfies `generalCollectiveRisks_nonempty` with the complete displayed premises. -/
lemma generalCollectiveRisks_nonempty (N : ℕ) (q : Fin 3 → ℝ) :
    (generalCollectiveRisks N q).Nonempty :=
  (collectiveRisks_nonempty N q).mono (jointRisks_subset_general N q)

/-- The stated copy-decision construction satisfies `generalCollectiveRisks_bddBelow` with the complete displayed premises. -/
lemma generalCollectiveRisks_bddBelow (N : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    BddBelow (generalCollectiveRisks N q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨P, rfl⟩
  exact P.error_nonneg q hq

/-- The stated copy-decision construction satisfies `collectiveOptimum_le_generalError` with the complete displayed premises. -/
lemma collectiveOptimum_le_generalError {N : ℕ} (P : GeneralCollectivePolicy N)
    (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) : collectiveOptimum N q ≤ P.error q := by
  letI := P.space
  by_contra h
  have hgap : 0 < collectiveOptimum N q-P.error q := sub_pos.2 (lt_of_not_ge h)
  have hQ : 0 ≤ ∑ i, q i := Finset.sum_nonneg (fun i _ => hq i)
  let ε : ℝ := (collectiveOptimum N q-P.error q)/(2*((∑ i, q i)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Λ, hΛ⟩ := P.measurement.randomized_finite_approximation P.guess P.measurable_guess q hq ε hε
  have hl : collectiveOptimum N q ≤ jointError Λ q :=
    csInf_le (collectiveRisks_bddBelow N q hq) ⟨Λ, rfl⟩
  have hu := (abs_le.1 hΛ).2
  have he : ε*(2*((∑ i, q i)+1))=collectiveOptimum N q-P.error q := by
    dsimp only [ε]
    exact div_mul_cancel₀ _ (by positivity : (2:ℝ)*((∑ i, q i)+1) ≠ 0)
  change jointError Λ q-P.error q ≤ _ at hu
  nlinarith only [hε, hl, hu, he, hQ]

/-- Genuine risk ranges agree in infimum for every nonnegative prior, including
zero and unnormalized priors. No optimum-attainment assumption is needed. -/
theorem generalCollectiveOptimum_eq_finite (N : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    generalCollectiveOptimum N q=collectiveOptimum N q := by
  apply le_antisymm
  · exact csInf_le_csInf (generalCollectiveRisks_bddBelow N q hq)
      (collectiveRisks_nonempty N q) (jointRisks_subset_general N q)
  · apply le_csInf (generalCollectiveRisks_nonempty N q)
    rintro _ ⟨P, rfl⟩
    exact collectiveOptimum_le_generalError P q hq

end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
