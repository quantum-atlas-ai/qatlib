/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.RiskCoarsening

/-!
# General Policy

Fresh Policies constructions for Copy Decision.
Defines `RawGeneralPolicy`, `generalLabelRisk`, `GeneralPolicyValid`.
Proves `terminal_prob_le_one`, `generalLabelRisk_unit`, `generalPolicyError_nonneg`.
-/


set_option autoImplicit false
noncomputable section
universe u
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Fixed-depth effect/continuation trees. The outcome space and its actual
POVM are stored at each node. No quantum output or hidden label indexes a child.
Full causal-kernel measurability is not encoded in this raw relaxation. -/
inductive RawGeneralPolicy : ℕ → Type (u+1) where
  | leaf (p : TerminalDecision) : RawGeneralPolicy 0
  | step {n : ℕ} (Y : Type u) (mY : MeasurableSpace Y)
      (M : @GeneralQubitPOVM Y mY) (next : Y → RawGeneralPolicy n) : RawGeneralPolicy (n+1)

/-- Label-wise Born risk, recursively evaluated on the SAME actual program. -/
def generalLabelRisk : {n : ℕ} → RawGeneralPolicy.{u} n → Fin 3 → ℝ
  | _, .leaf p, i => 1-p.prob i
  | _, .step _ mY M next, i =>
      letI := mY
      ∫ y, generalLabelRisk (next y) i ∂M.bornMeasure (trineState i)

/-- This relaxation checks measurability of risks DERIVED from actual children,
not the complete history/output kernel. It may include more trees than the
physical protocol class; that class still needs a risk-preserving embedding.
It supplies neither a risk oracle nor an error inequality. -/
def GeneralPolicyValid : {n : ℕ} → RawGeneralPolicy.{u} n → Prop
  | _, .leaf _ => True
  | _, .step _ mY _ next =>
      letI := mY
      (∀ y, GeneralPolicyValid (next y)) ∧
        (∀ i, Measurable (fun y => generalLabelRisk (next y) i))

/-- The stated copy-decision construction satisfies `terminal_prob_le_one` with the complete displayed premises. -/
lemma terminal_prob_le_one (p : TerminalDecision) (i : Fin 3) : p.prob i ≤ 1 := by
  have h : p.prob i ≤ ∑ k, p.prob k :=
    Finset.single_le_sum (fun k _ => p.nonneg k) (Finset.mem_univ i)
  rwa [p.total] at h

/-- Boundedness and integrability are proved from actual node probabilities,
preventing the totalized integral of a nonintegrable function from becoming risk. -/
theorem generalLabelRisk_unit {n : ℕ} (P : RawGeneralPolicy.{u} n)
    (hP : GeneralPolicyValid P) (i : Fin 3) :
    0 ≤ generalLabelRisk P i ∧ generalLabelRisk P i ≤ 1 := by
  induction P with
  | leaf p =>
    change 0 ≤ 1-p.prob i ∧ 1-p.prob i ≤ 1
    exact ⟨sub_nonneg.mpr (terminal_prob_le_one p i), by linarith [p.nonneg i]⟩
  | step Y mY M next ih =>
    letI := mY
    have hc : ∀ y, 0 ≤ generalLabelRisk (next y) i ∧ generalLabelRisk (next y) i ≤ 1 :=
      fun y => ih y (hP.1 y)
    have hint := integrable_unitRisk (M.bornMeasure (trineState i))
      (fun y => generalLabelRisk (next y) i) (hP.2 i) hc
    change 0 ≤ (∫ y, generalLabelRisk (next y) i ∂M.bornMeasure (trineState i)) ∧
      (∫ y, generalLabelRisk (next y) i ∂M.bornMeasure (trineState i)) ≤ 1
    refine ⟨integral_nonneg (fun y => (hc y).1), ?_⟩
    have hu := integral_mono hint (integrable_const (1:ℝ)) (fun y => (hc y).2)
    simpa only [integral_const, probReal_univ, one_smul] using hu

/-- Data and hypotheses for General Policy in the Fresh Policies construction. -/
structure GeneralPolicy (n : ℕ) where
  program : RawGeneralPolicy.{u} n
  valid : GeneralPolicyValid program

/-- Definition of general Policy Error in the Fresh Policies construction. -/
def generalPolicyError {n : ℕ} (P : RawGeneralPolicy.{u} n) (q : Fin 3 → ℝ) : ℝ :=
  ∑ i, q i*generalLabelRisk P i

/-- The stated copy-decision construction satisfies `generalPolicyError_nonneg` with the complete displayed premises. -/
lemma generalPolicyError_nonneg {n : ℕ} (P : RawGeneralPolicy.{u} n)
    (hP : GeneralPolicyValid P) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ generalPolicyError P q :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (generalLabelRisk_unit P hP i).1)

/-- Label risk of an actual finite POVM tree, independently of a prior. -/
def finiteLabelRisk : {n : ℕ} → FinitePOVMPolicy n → Fin 3 → ℝ
  | _, .leaf p, i => 1-p.prob i
  | _, .step _ Λ next, i =>
      ∑ a, qubitBorn (Λ.mats a) (trineState i)*finiteLabelRisk (next a) i

/-- The stated copy-decision construction satisfies `povmPolicyError_linear` with the complete displayed premises. -/
theorem povmPolicyError_linear {n : ℕ} (P : FinitePOVMPolicy n) (q : Fin 3 → ℝ) :
    povmPolicyError P q=∑ i, q i*finiteLabelRisk P i := by
  induction P generalizing q with
  | leaf p => rfl
  | step m Λ next ih =>
    simp only [povmPolicyError, finiteLabelRisk]
    simp_rw [ih]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
