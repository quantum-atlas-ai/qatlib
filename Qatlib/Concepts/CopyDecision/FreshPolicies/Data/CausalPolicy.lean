/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.GeneralOptimum
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Causal Policy

Fresh Policies constructions for Copy Decision.
Defines `QubitPOVMKernel`, `QubitPOVMKernel.trineKernel`, `CausalPolicy`.
Proves `CausalPolicy.labelRisk_eq_raw`, `CausalPolicy.validAndMeasurable`, `CausalPolicy.error_eq_raw`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory ProbabilityTheory

/-- Actual qubit measurement controlled by a classical measurable memory.
Measurability holds for EVERY outcome event and input, not just final risks. -/
structure QubitPOVMKernel (H Y : Type) [MeasurableSpace H] [MeasurableSpace Y] where
  measurement : H → GeneralQubitPOVM Y
  measurable_born : ∀ (x : Qubit) (B : Set Y), MeasurableSet B →
    Measurable (fun h => (measurement h).bornMeasure x B)

/-- Definition of trine Kernel in the Fresh Policies construction. -/
def QubitPOVMKernel.trineKernel {H Y : Type} [MeasurableSpace H] [MeasurableSpace Y]
    (M : QubitPOVMKernel H Y) (i : Fin 3) : Kernel H Y where
  toFun h := (M.measurement h).bornMeasure (trineState i)
  measurable' := Measure.measurable_of_measurable_coe _ (M.measurable_born (trineState i))

/-- Typeclass instance for trine Kernel markov in the Fresh Policies construction. -/
instance QubitPOVMKernel.trineKernel_markov {H Y : Type} [MeasurableSpace H] [MeasurableSpace Y]
    (M : QubitPOVMKernel H Y) (i : Fin 3) : IsMarkovKernel (M.trineKernel i) where
  isProbabilityMeasure h := GeneralQubitPOVM.trineBorn_probability (M.measurement h) i

/-- Operational fixed-depth controllers. All controls are classical measurable
memories, observations are actual full Born kernels, and memory updates are
measurable. No measured quantum output is passed to the next fresh-copy step.
Memory/outcome types may change from one stage to the next. -/
inductive CausalPolicy : ℕ → (H : Type) → [MeasurableSpace H] → Type 1 where
  | leaf {H : Type} [MeasurableSpace H] (p : H → TerminalDecision)
      (meas : ∀ k, Measurable (fun h => (p h).prob k)) : CausalPolicy 0 H
  | step {n : ℕ} {H : Type} [MeasurableSpace H] (Y H' : Type)
      [MeasurableSpace Y] [MeasurableSpace H'] (M : QubitPOVMKernel H Y)
      (update : H × Y → H') (meas : Measurable update)
      (next : CausalPolicy n H') : CausalPolicy (n+1) H
  /-- Measurable classical dispatch consumes no copy; the finite branch selects
  a fixed program, without retaining a quantum output or an unknown label. -/
  | dispatch {n : ℕ} {H : Type} [MeasurableSpace H] (m : ℕ)
      (pick : H → Fin m) (meas : Measurable pick)
      (branches : Fin m → CausalPolicy n Unit) : CausalPolicy n H
  /-- A measurable classical choice retains the complete current memory. -/
  | choose {n : ℕ} {H : Type} [MeasurableSpace H] (pick : H → Bool)
      (meas : Measurable pick) (yes no : CausalPolicy n H) : CausalPolicy n H

/-- Definition of to Raw in the Fresh Policies construction. -/
def CausalPolicy.toRaw : {n : ℕ} → {H : Type} → [MeasurableSpace H] →
    CausalPolicy n H → H → RawGeneralPolicy.{0} n
  | _, _, _, @CausalPolicy.leaf H mH p _, h => RawGeneralPolicy.leaf (p h)
  | _, _, _, @CausalPolicy.step d H mH Y _H' mY _mH' M update _ next, h =>
      @RawGeneralPolicy.step d Y mY (M.measurement h) (fun y => next.toRaw (update (h, y)))
  | _, _, _, @CausalPolicy.dispatch d H mH _m pick _ branches, h => (branches (pick h)).toRaw ()
  | _, _, _, @CausalPolicy.choose _d _H _mH pick _ yes no, h =>
      if pick h then yes.toRaw h else no.toRaw h

/-- Independent operational evaluation through the complete observation kernel. -/
def causalLabelRisk : {n : ℕ} → {H : Type} → [MeasurableSpace H] →
    CausalPolicy n H → H → Fin 3 → ℝ
  | _, _, _, @CausalPolicy.leaf H mH p _, h, i => 1-(p h).prob i
  | _, _, _, @CausalPolicy.step d H mH _Y _H' _mY _mH' M update _ next, h, i =>
      ∫ y, causalLabelRisk next (update (h, y)) i ∂M.trineKernel i h
  | _, _, _, @CausalPolicy.dispatch d H mH _m pick _ branches, h, i =>
      causalLabelRisk (branches (pick h)) () i
  | _, _, _, @CausalPolicy.choose _d _H _mH pick _ yes no, h, i =>
      if pick h then causalLabelRisk yes h i else causalLabelRisk no h i

/-- The stated copy-decision construction satisfies `CausalPolicy.labelRisk_eq_raw` with the complete displayed premises. -/
theorem CausalPolicy.labelRisk_eq_raw {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (h : H) (i : Fin 3) :
    causalLabelRisk P h i=generalLabelRisk (P.toRaw h) i := by
  induction P with
  | leaf _ _ => rfl
  | step Y H' M update meas next ih =>
    change (∫ y, causalLabelRisk next (update (h, y)) i
      ∂(M.measurement h).bornMeasure (trineState i)) = _
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => ih (update (h, y)))
  | dispatch m pick meas branches ih => exact ih (pick h) ()
  | choose pick meas yes no ihY ihN =>
    by_cases hc : pick h=true
    · simpa only [causalLabelRisk, CausalPolicy.toRaw, if_pos hc] using ihY h
    · simpa only [causalLabelRisk, CausalPolicy.toRaw, if_neg hc] using ihN h

/-- Full physical measurability implies the weaker derived-risk predicate.
The proof uses native Markov-kernel integration, not a supplied risk function. -/
theorem CausalPolicy.validAndMeasurable {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) :
    (∀ h, GeneralPolicyValid (P.toRaw h)) ∧
      (∀ i, Measurable (fun h => generalLabelRisk (P.toRaw h) i)) := by
  classical
  induction P with
  | leaf p meas =>
    constructor
    · intro h
      trivial
    · intro i
      exact measurable_const.sub (meas i)
  | step Y H' M update meas next ih =>
    constructor
    · intro h
      constructor
      · intro y
        exact ih.1 (update (h, y))
      · intro i
        exact (ih.2 i).comp (meas.comp (measurable_const.prodMk measurable_id))
    · intro i
      have hm : Measurable (fun z => generalLabelRisk (next.toRaw (update z)) i) :=
        (ih.2 i).comp meas
      exact (hm.stronglyMeasurable.integral_kernel_prod_right'
        (κ := M.trineKernel i)).measurable
  | dispatch m pick meas branches ih =>
    constructor
    · intro h
      exact (ih (pick h)).1 ()
    · intro i
      exact (measurable_of_finite (fun a : Fin m =>
        generalLabelRisk ((branches a).toRaw ()) i)).comp meas
  | choose pick meas yes no ihY ihN =>
    constructor
    · intro h
      change GeneralPolicyValid (if pick h then yes.toRaw h else no.toRaw h)
      split_ifs
      · exact ihY.1 h
      · exact ihN.1 h
    · intro i
      have hm : Measurable ((pick ⁻¹' {true}).piecewise
          (fun h => generalLabelRisk (yes.toRaw h) i)
          (fun h => generalLabelRisk (no.toRaw h) i)) :=
        (ihY.2 i).piecewise (meas (MeasurableSet.singleton true)) (ihN.2 i)
      convert hm using 1
      funext h
      by_cases hc : pick h=true <;> simp [CausalPolicy.toRaw, Set.piecewise, hc]

/-- Definition of causal Policy Error in the Fresh Policies construction. -/
def causalPolicyError {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (h : H) (q : Fin 3 → ℝ) : ℝ := ∑ i, q i*causalLabelRisk P h i

/-- The stated copy-decision construction satisfies `CausalPolicy.error_eq_raw` with the complete displayed premises. -/
theorem CausalPolicy.error_eq_raw {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (h : H) (q : Fin 3 → ℝ) :
    causalPolicyError P h q=generalPolicyError (P.toRaw h) q := by
  unfold causalPolicyError generalPolicyError
  simp_rw [P.labelRisk_eq_raw]

/-- Uniform lower bound now consumes a controller whose complete observation
kernel and classical updates are measurable. This does not classify arbitrary
ancillary instruments or prove every alternative protocol presentation equivalent. -/
theorem causalPolicy_uniform_lower {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy (n+1) H) (h : H) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ causalPolicyError P h (fun _ => 1/3) := by
  rw [P.error_eq_raw]
  exact generalPolicy_uniform_lower (P.toRaw h) (P.validAndMeasurable.1 h)

/-- Every finite adaptive POVM tree is a native measurable controller. Finite
classical dispatch freezes the actual branch program without consuming a copy. -/
def FinitePOVMPolicy.toCausal : {n : ℕ} → FinitePOVMPolicy n → CausalPolicy n Unit
  | _, .leaf p => .leaf (fun _ => p) (fun _ => measurable_const)
  | _, .step m Λ next => .step (Fin m) (Fin m)
      ⟨(fun _ => GeneralQubitPOVM.ofFinite Λ), (by intro x B hB; exact measurable_const)⟩
      Prod.snd measurable_snd
      (.dispatch m id measurable_id (fun a => (next a).toCausal))

/-- The stated copy-decision construction satisfies `FinitePOVMPolicy.toCausal_raw` with the complete displayed premises. -/
theorem FinitePOVMPolicy.toCausal_raw {n : ℕ} (F : FinitePOVMPolicy n) :
    F.toCausal.toRaw ()=F.toGeneral := by
  induction F with
  | leaf _ => rfl
  | step m Λ next ih =>
    dsimp only [FinitePOVMPolicy.toCausal, CausalPolicy.toRaw, FinitePOVMPolicy.toGeneral]
    congr 1
    funext a
    exact ih a

/-- The stated copy-decision construction satisfies `FinitePOVMPolicy.toCausal_error` with the complete displayed premises. -/
theorem FinitePOVMPolicy.toCausal_error {n : ℕ} (F : FinitePOVMPolicy n) (q : Fin 3 → ℝ) :
    causalPolicyError F.toCausal () q=povmPolicyError F q := by
  rw [CausalPolicy.error_eq_raw, F.toCausal_raw, F.toGeneral_error]

/-- Risk range of the native classical-memory/full-observation-kernel model.
The initial memory is a single fixed classical value independent of the label. -/
def causalPolicyRisks (n : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  {E | ∃ (H : Type) (mH : MeasurableSpace H) (P : @CausalPolicy n H mH) (h : H),
    causalPolicyError P h q=E}

/-- Definition of causal Policy Optimum in the Fresh Policies construction. -/
def causalPolicyOptimum (n : ℕ) (q : Fin 3 → ℝ) : ℝ := sInf (causalPolicyRisks n q)

/-- The stated copy-decision construction satisfies `finiteRisks_subset_causal` with the complete displayed premises. -/
lemma finiteRisks_subset_causal (n : ℕ) (q : Fin 3 → ℝ) :
    finitePOVMRisks n q ⊆ causalPolicyRisks n q := by
  rintro _ ⟨F, rfl⟩
  exact ⟨Unit, inferInstance, F.toCausal, (), F.toCausal_error q⟩

/-- The stated copy-decision construction satisfies `causalRisks_subset_general` with the complete displayed premises. -/
lemma causalRisks_subset_general (n : ℕ) (q : Fin 3 → ℝ) :
    causalPolicyRisks n q ⊆ generalPolicyRisks n q := by
  rintro _ ⟨H, mH, P, h, rfl⟩
  exact ⟨⟨P.toRaw h, P.validAndMeasurable.1 h⟩, (P.error_eq_raw h q).symm⟩

/-- The stated copy-decision construction satisfies `causalPolicyOptimum_eq_finite` with the complete displayed premises. -/
theorem causalPolicyOptimum_eq_finite (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    causalPolicyOptimum n q=finitePOVMOptimum n q :=
  physicalRiskSet_optimum q hq _ (finiteRisks_subset_causal n q) (causalRisks_subset_general n q)

/-- The stated copy-decision construction satisfies `causalPolicyOptimum_uniform_lower` with the complete displayed premises. -/
theorem causalPolicyOptimum_uniform_lower (n : ℕ) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ causalPolicyOptimum (n+1) (fun _ => 1/3) := by
  rw [causalPolicyOptimum_eq_finite _ _ (by intro i; norm_num)]
  exact finitePOVMOptimum_uniform_lower n

/-- The stated copy-decision construction satisfies `CausalPolicy.error_measurable` with the complete displayed premises. -/
theorem CausalPolicy.error_measurable {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy n H) (q : Fin 3 → ℝ) : Measurable (fun h => causalPolicyError P h q) := by
  unfold causalPolicyError
  apply Finset.measurable_fun_sum
  intro i _
  apply measurable_const.mul
  simpa only [P.labelRisk_eq_raw] using P.validAndMeasurable.2 i

/-- External classical randomization uses the SAME initial-memory law for all
hidden labels and consumes no copies. Every pointwise controller lower bound
therefore survives arbitrary such randomization. -/
theorem causalPolicy_randomized_uniform_lower {n : ℕ} {H : Type} [MeasurableSpace H]
    (P : CausalPolicy (n+1) H) (ν : Measure H) [IsProbabilityMeasure ν] :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ ∫ h, causalPolicyError P h (fun _ => 1/3) ∂ν := by
  have hc : ∀ h, 0 ≤ causalPolicyError P h (fun _ => 1/3) ∧
      causalPolicyError P h (fun _ => 1/3) ≤ 1 := by
    intro h
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
  have hint := integrable_unitRisk ν _ (P.error_measurable _) hc
  have hl := integral_mono
    (integrable_const ((1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n))) hint
    (fun h => causalPolicy_uniform_lower P h)
  simpa only [integral_const, probReal_univ, one_smul] using hl

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
