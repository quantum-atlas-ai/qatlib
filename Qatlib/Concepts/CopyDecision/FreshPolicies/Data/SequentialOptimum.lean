/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.ControllerPresentations

/-!
# Sequential Optimum

Fresh Policies constructions for Copy Decision.
Defines `CausalProgramMixture`, `CausalProgramMixture.error`, `CausalProgramMixture.ofCausal`.
Proves `CausalProgramMixture.ofCausal_error`, `CausalProgramMixture.optimum_le_error`, `causalRisks_subset_mixture`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- A common classical seed law selects valid full-kernel controllers, possibly
with different memory types. Requiring only the actual averaged error to be
measurable is a safe enlargement for a lower bound; full seed-to-output kernel
measurability is not asserted by this structure. -/
structure CausalProgramMixture (N : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  Memory : Seed → Type
  memorySpace : (s : Seed) → MeasurableSpace (Memory s)
  program : (s : Seed) → @CausalPolicy N (Memory s) (memorySpace s)
  initial : (s : Seed) → Memory s
  measurable_error : @Measurable Seed ℝ seedSpace inferInstance
    (fun s => @causalPolicyError N (Memory s) (memorySpace s) (program s) (initial s) (fun _ => 1/3))

/-- Definition of error in the Fresh Policies construction. -/
def CausalProgramMixture.error {N : ℕ} (P : CausalProgramMixture N) : ℝ := by
  letI := P.seedSpace
  exact ∫ s, @causalPolicyError N (P.Memory s) (P.memorySpace s)
    (P.program s) (P.initial s) (fun _ => 1/3) ∂P.law

/-- Definition of of Causal in the Fresh Policies construction. -/
def CausalProgramMixture.ofCausal {N : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy N H) (h : H) : CausalProgramMixture N where
  Seed := Unit
  seedSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance
  Memory _ := H
  memorySpace _ := inferInstance
  program _ := P
  initial _ := h
  measurable_error := measurable_const

/-- The stated copy-decision construction satisfies `CausalProgramMixture.ofCausal_error` with the complete displayed premises. -/
lemma CausalProgramMixture.ofCausal_error {N : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy N H) (h : H) :
    (CausalProgramMixture.ofCausal P h).error=causalPolicyError P h (fun _ => 1/3) := by
  change (∫ _s : Unit, causalPolicyError P h (fun _ => (1/3:ℝ)) ∂Measure.dirac ())=_
  rw [integral_const]
  simp

/-- The stated copy-decision construction satisfies `CausalProgramMixture.optimum_le_error` with the complete displayed premises. -/
lemma CausalProgramMixture.optimum_le_error {N : ℕ} (P : CausalProgramMixture N) :
    causalPolicyOptimum N (fun _ => 1/3) ≤ P.error := by
  letI := P.seedSpace
  letI : ∀ s, MeasurableSpace (P.Memory s) := P.memorySpace
  letI := P.probability
  have hb : BddBelow (causalPolicyRisks N (fun _ => (1/3:ℝ))) :=
    (generalPolicyRisks_bddBelow N _ (by intro i; norm_num)).mono (causalRisks_subset_general N _)
  have hint := integrable_unitRisk P.law _ P.measurable_error
    (fun s => causalPolicyError_unit (P.program s) (P.initial s))
  have hl := integral_mono (integrable_const (causalPolicyOptimum N (fun _ => (1/3:ℝ)))) hint
    (fun s => csInf_le hb ⟨P.Memory s, P.memorySpace s, P.program s, P.initial s, rfl⟩)
  simpa only [CausalProgramMixture.error, integral_const, probReal_univ, one_smul] using hl

/-- Definition of mixture Risks in the Fresh Policies construction. -/
def mixtureRisks (N : ℕ) : Set ℝ := Set.range (fun P : CausalProgramMixture N => P.error)
/-- Definition of mixture Optimum in the Fresh Policies construction. -/
def mixtureOptimum (N : ℕ) : ℝ := sInf (mixtureRisks N)

/-- The stated copy-decision construction satisfies `causalRisks_subset_mixture` with the complete displayed premises. -/
lemma causalRisks_subset_mixture (N : ℕ) : causalPolicyRisks N (fun _ => 1/3) ⊆ mixtureRisks N := by
  rintro _ ⟨H, mH, P, h, rfl⟩
  exact ⟨CausalProgramMixture.ofCausal P h, CausalProgramMixture.ofCausal_error P h⟩

/-- The stated copy-decision construction satisfies `mixtureRisks_nonempty` with the complete displayed premises. -/
lemma mixtureRisks_nonempty (N : ℕ) : (mixtureRisks N).Nonempty :=
  ((finitePOVMRisks_nonempty N _).mono (finiteRisks_subset_causal N _)).mono
    (causalRisks_subset_mixture N)

/-- The stated copy-decision construction satisfies `mixtureRisks_bddBelow` with the complete displayed premises. -/
lemma mixtureRisks_bddBelow (N : ℕ) : BddBelow (mixtureRisks N) := by
  refine ⟨causalPolicyOptimum N (fun _ => 1/3), ?_⟩
  rintro _ ⟨P, rfl⟩
  exact P.optimum_le_error

/-- External random selection cannot improve the infimum; deterministic
controllers embed as actual Dirac mixtures. This also controls any physical
subclass lying between the two explicitly defined classes. -/
theorem mixtureOptimum_eq_causal (N : ℕ) : mixtureOptimum N=causalPolicyOptimum N (fun _ => 1/3) := by
  apply le_antisymm
  · exact csInf_le_csInf (mixtureRisks_bddBelow N)
      ((finitePOVMRisks_nonempty N _).mono (finiteRisks_subset_causal N _)) (causalRisks_subset_mixture N)
  · apply le_csInf (mixtureRisks_nonempty N)
    rintro _ ⟨P, rfl⟩
    exact P.optimum_le_error

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
