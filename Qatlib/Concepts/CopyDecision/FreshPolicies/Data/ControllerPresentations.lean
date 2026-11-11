/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.CausalPolicy

/-!
# Controller Presentations

Fresh Policies constructions for Copy Decision.
Defines `idleObservation`, `CausalPolicy.ignoreCopy`, `paddedTerminal`.
Proves `CausalPolicy.ignoreCopy_labelRisk`, `paddedTerminal_labelRisk`, `StoppingPolicy.toCausal_labelRisk`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory ProbabilityTheory

/-- Definition of idle Observation in the Fresh Policies construction. -/
def idleObservation (H : Type) [MeasurableSpace H] : QubitPOVMKernel H (Fin 1) where
  measurement _ := GeneralQubitPOVM.ofFinite identityPOVM
  measurable_born := by intro x B hB; exact measurable_const

/-- Definition of ignore Copy in the Fresh Policies construction. -/
def CausalPolicy.ignoreCopy {n : ℕ} {H : Type} [MeasurableSpace H] (P : CausalPolicy n H) :
    CausalPolicy (n+1) H := .step (Fin 1) H (idleObservation H) Prod.fst measurable_fst P

/-- The stated copy-decision construction satisfies `CausalPolicy.ignoreCopy_labelRisk` with the complete displayed premises. -/
lemma CausalPolicy.ignoreCopy_labelRisk {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (h : H) (i : Fin 3) :
    causalLabelRisk P.ignoreCopy h i=causalLabelRisk P h i := by
  change (∫ _y, causalLabelRisk P h i ∂(idleObservation H).trineKernel i h)=_
  simp only [integral_const, probReal_univ, one_smul]

/-- Definition of padded Terminal in the Fresh Policies construction. -/
def paddedTerminal {H : Type} [MeasurableSpace H] (p : H → TerminalDecision)
    (meas : ∀ i, Measurable (fun h => (p h).prob i)) : (n : ℕ) → CausalPolicy n H
  | 0 => .leaf p meas
  | n+1 => (paddedTerminal p meas n).ignoreCopy

/-- The stated copy-decision construction satisfies `paddedTerminal_labelRisk` with the complete displayed premises. -/
lemma paddedTerminal_labelRisk {H : Type} [MeasurableSpace H] (p : H → TerminalDecision)
    (meas : ∀ i, Measurable (fun h => (p h).prob i)) (n : ℕ) (h : H) (i : Fin 3) :
    causalLabelRisk (paddedTerminal p meas n) h i=1-(p h).prob i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ((paddedTerminal p meas n).ignoreCopy_labelRisk h i).trans ih

/-- Bounded early stopping uses the same full observation kernels and classical
updates as the native controller. A terminal decision may occur at any depth. -/
inductive StoppingPolicy : ℕ → (H : Type) → [MeasurableSpace H] → Type 1 where
  | done {n : ℕ} {H : Type} [MeasurableSpace H] (p : H → TerminalDecision)
      (meas : ∀ i, Measurable (fun h => (p h).prob i)) : StoppingPolicy n H
  | step {n : ℕ} {H : Type} [MeasurableSpace H] (Y H' : Type)
      [MeasurableSpace Y] [MeasurableSpace H'] (M : QubitPOVMKernel H Y)
      (update : H × Y → H') (meas : Measurable update)
      (next : StoppingPolicy n H') : StoppingPolicy (n+1) H
  | dispatch {n : ℕ} {H : Type} [MeasurableSpace H] (m : ℕ)
      (pick : H → Fin m) (meas : Measurable pick)
      (branches : Fin m → StoppingPolicy n Unit) : StoppingPolicy n H
  | choose {n : ℕ} {H : Type} [MeasurableSpace H] (pick : H → Bool)
      (meas : Measurable pick) (yes no : StoppingPolicy n H) : StoppingPolicy n H

/-- Definition of to Causal in the Fresh Policies construction. -/
def StoppingPolicy.toCausal : {n : ℕ} → {H : Type} → [MeasurableSpace H] →
    StoppingPolicy n H → CausalPolicy n H
  | _, _, _, @StoppingPolicy.done n _H _mH p meas => paddedTerminal p meas n
  | _, _, _, @StoppingPolicy.step _d _H _mH Y H' _mY _mH' M update meas next =>
      .step Y H' M update meas next.toCausal
  | _, _, _, @StoppingPolicy.dispatch _d _H _mH m pick meas branches =>
      .dispatch m pick meas (fun a => (branches a).toCausal)
  | _, _, _, @StoppingPolicy.choose _d _H _mH pick meas yes no =>
      .choose pick meas yes.toCausal no.toCausal

/-- Definition of stopping Label Risk in the Fresh Policies construction. -/
def stoppingLabelRisk : {n : ℕ} → {H : Type} → [MeasurableSpace H] →
    StoppingPolicy n H → H → Fin 3 → ℝ
  | _, _, _, @StoppingPolicy.done _d _H _mH p _, h, i => 1-(p h).prob i
  | _, _, _, @StoppingPolicy.step _d _H _mH _Y _H' _mY _mH' M update _ next, h, i =>
      ∫ y, stoppingLabelRisk next (update (h,y)) i ∂M.trineKernel i h
  | _, _, _, @StoppingPolicy.dispatch _d _H _mH _m pick _ branches, h, i =>
      stoppingLabelRisk (branches (pick h)) () i
  | _, _, _, @StoppingPolicy.choose _d _H _mH pick _ yes no, h, i =>
      if pick h then stoppingLabelRisk yes h i else stoppingLabelRisk no h i

/-- The stated copy-decision construction satisfies `StoppingPolicy.toCausal_labelRisk` with the complete displayed premises. -/
theorem StoppingPolicy.toCausal_labelRisk {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : StoppingPolicy n H) (h : H) (i : Fin 3) :
    causalLabelRisk P.toCausal h i=stoppingLabelRisk P h i := by
  induction P with
  | done p meas => exact paddedTerminal_labelRisk p meas _ h i
  | step Y H' M update meas next ih =>
    change (∫ y, causalLabelRisk next.toCausal (update (h,y)) i ∂M.trineKernel i h)=_
    simp_rw [ih]
    rfl
  | dispatch m pick meas branches ih => exact ih (pick h) ()
  | choose pick meas yes no ihY ihN =>
    by_cases hc : pick h=true
    · simpa only [StoppingPolicy.toCausal, causalLabelRisk, stoppingLabelRisk, if_pos hc] using ihY h
    · simpa only [StoppingPolicy.toCausal, causalLabelRisk, stoppingLabelRisk, if_neg hc] using ihN h

/-- The stated copy-decision construction satisfies `stoppingPolicy_uniform_lower` with the complete displayed premises. -/
theorem stoppingPolicy_uniform_lower {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : StoppingPolicy (n+1) H) (h : H) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ ∑ i, (1/3:ℝ)*stoppingLabelRisk P h i := by
  simpa only [causalPolicyError, P.toCausal_labelRisk] using causalPolicy_uniform_lower P.toCausal h

/-- The stated copy-decision construction satisfies `causalPolicyError_unit` with the complete displayed premises. -/
lemma causalPolicyError_unit {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (h : H) :
    0 ≤ causalPolicyError P h (fun _ => 1/3) ∧ causalPolicyError P h (fun _ => 1/3) ≤ 1 := by
  constructor
  · rw [P.error_eq_raw]
    exact generalPolicyError_nonneg _ (P.validAndMeasurable.1 h) _ (by intro i; norm_num)
  · unfold causalPolicyError
    calc
      _ ≤ ∑ _i : Fin 3, (1/3:ℝ)*1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by
          rw [P.labelRisk_eq_raw]
          exact (generalLabelRisk_unit _ (P.validAndMeasurable.1 h) i).2) (by norm_num)
      _ = 1 := by norm_num [Fin.sum_univ_three]

/-- An external seed can select entire different programs and memory types.
The same seed law is outside the hidden-label average. Only measurability of
the actually evaluated error is required to average already valid programs. -/
theorem causalPolicy_family_uniform_lower {n : ℕ} {S : Type} [MeasurableSpace S]
    {H : S → Type} [∀ s, MeasurableSpace (H s)]
    (P : (s : S) → CausalPolicy (n+1) (H s)) (h : (s : S) → H s)
    (ν : Measure S) [IsProbabilityMeasure ν]
    (meas : Measurable (fun s => causalPolicyError (P s) (h s) (fun _ => 1/3))) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤
      ∫ s, causalPolicyError (P s) (h s) (fun _ => 1/3) ∂ν := by
  have hint := integrable_unitRisk ν _ meas (fun s => causalPolicyError_unit (P s) (h s))
  have hl := integral_mono
    (integrable_const ((1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n))) hint
    (fun s => causalPolicy_uniform_lower (P s) (h s))
  simpa only [integral_const, probReal_univ, one_smul] using hl

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
