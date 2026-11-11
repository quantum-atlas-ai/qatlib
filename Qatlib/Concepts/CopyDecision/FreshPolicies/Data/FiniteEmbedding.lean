/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.GeneralApproximation
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite Embedding

Fresh Policies constructions for Copy Decision.
Defines `GeneralQubitPOVM.ofFinite`, `FinitePOVMPolicy.toGeneral`, `FinitePOVMPolicy.asGeneral`.
Proves `GeneralQubitPOVM.ofFinite_singleton`, `GeneralQubitPOVM.ofFinite_born_singleton`, `FinitePOVMPolicy.toGeneral_valid`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- A finite physical POVM as an actual countably additive effect measure. -/
def GeneralQubitPOVM.ofFinite {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) : GeneralQubitPOVM (Fin m) where
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

/-- The stated copy-decision construction satisfies `GeneralQubitPOVM.ofFinite_singleton` with the complete displayed premises. -/
lemma GeneralQubitPOVM.ofFinite_singleton {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) (a : Fin m) :
    (GeneralQubitPOVM.ofFinite Λ).effects {a}=Λ.mats a := by
  simp [GeneralQubitPOVM.ofFinite, VectorMeasure.dirac]

/-- The stated copy-decision construction satisfies `GeneralQubitPOVM.ofFinite_born_singleton` with the complete displayed premises. -/
lemma GeneralQubitPOVM.ofFinite_born_singleton {m : ℕ}
    (Λ : POVM (Fin m) (Fin 2)) (a : Fin m) (x : Qubit) :
    ((GeneralQubitPOVM.ofFinite Λ).bornMeasure x).real {a}=qubitBorn (Λ.mats a) x := by
  rw [GeneralQubitPOVM.bornMeasure_real _ _ (measurableSet_singleton _),
    GeneralQubitPOVM.ofFinite_singleton]

/-- Definition of to General in the Fresh Policies construction. -/
def FinitePOVMPolicy.toGeneral : {n : ℕ} → FinitePOVMPolicy n → RawGeneralPolicy.{0} n
  | _, .leaf p => .leaf p
  | _, .step m Λ next =>
      .step (Fin m) inferInstance (GeneralQubitPOVM.ofFinite Λ) (fun a => (next a).toGeneral)

/-- The stated copy-decision construction satisfies `FinitePOVMPolicy.toGeneral_valid` with the complete displayed premises. -/
theorem FinitePOVMPolicy.toGeneral_valid {n : ℕ} (P : FinitePOVMPolicy n) :
    GeneralPolicyValid P.toGeneral := by
  induction P with
  | leaf _ => trivial
  | step m Λ next ih =>
    constructor
    · exact ih
    · intro i
      exact measurable_of_finite _

/-- Every actual label risk is preserved, not only one selected prior. -/
theorem FinitePOVMPolicy.toGeneral_labelRisk {n : ℕ} (P : FinitePOVMPolicy n) (i : Fin 3) :
    generalLabelRisk P.toGeneral i=finiteLabelRisk P i := by
  induction P with
  | leaf _ => rfl
  | step m Λ next ih =>
    change (∫ a, generalLabelRisk (next a).toGeneral i
      ∂(GeneralQubitPOVM.ofFinite Λ).bornMeasure (trineState i)) = _
    have hint := integrable_unitRisk
      ((GeneralQubitPOVM.ofFinite Λ).bornMeasure (trineState i))
      (fun a => generalLabelRisk (next a).toGeneral i) (measurable_of_finite _)
      (fun a => generalLabelRisk_unit _ (next a).toGeneral_valid i)
    rw [integral_fintype hint]
    simp only [GeneralQubitPOVM.ofFinite_born_singleton, ih, smul_eq_mul, finiteLabelRisk]

/-- The stated copy-decision construction satisfies `FinitePOVMPolicy.toGeneral_error` with the complete displayed premises. -/
theorem FinitePOVMPolicy.toGeneral_error {n : ℕ} (P : FinitePOVMPolicy n) (q : Fin 3 → ℝ) :
    generalPolicyError P.toGeneral q=povmPolicyError P q := by
  unfold generalPolicyError
  simp_rw [P.toGeneral_labelRisk]
  exact (povmPolicyError_linear P q).symm

/-- Definition of as General in the Fresh Policies construction. -/
def FinitePOVMPolicy.asGeneral {n : ℕ} (P : FinitePOVMPolicy n) : GeneralPolicy.{0} n :=
  ⟨P.toGeneral, P.toGeneral_valid⟩

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
