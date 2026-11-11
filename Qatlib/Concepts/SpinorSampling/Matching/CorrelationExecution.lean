/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.CorrelationPlan

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Correlation Execution

Correlation Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Types contain exactly the fresh cohorts actually requested in each mode. -/
def CorrelationData (S : Type) (mode : CorrelationMode) (n K : ℕ) : Type :=
  match mode with
  | .zero => Unit
  | .matched => (Fin n → S × Bool) × (Fin n → S × Bool)
  | .matchedMedian => Fin K → ((Fin n → S × Bool) × (Fin n → S × Bool))
  | .ustatisticMedian => Fin K → Fin n → S × Bool

instance {S : Type} [Fintype S] (mode : CorrelationMode) (n K : ℕ) :
    Fintype (CorrelationData S mode n K) := by
  cases mode <;> dsimp only [CorrelationData] <;> infer_instance

instance {S : Type} [DecidableEq S] (mode : CorrelationMode) (n K : ℕ) :
    DecidableEq (CorrelationData S mode n K) := by
  cases mode <;> dsimp only [CorrelationData] <;> infer_instance

variable {S : Type} [DecidableEq S]

/-- Construction for correlation Output Q in the correlation execution model. -/
def correlationOutputQ (mode : CorrelationMode) (n K M : ℕ) (τ : S → S) (lo : ℚ) :
    CorrelationData S mode n K → ℚ :=
  match mode with
  | .zero => fun _ => 0
  | .matched => fun z => intervalClipQ lo 1 (matchedStatisticQ z.1 z.2 τ)
  | .matchedMedian => fun ω =>
      intervalClipQ lo 1 (rawBlockMedianQ (fun z => matchedStatisticQ z.1 z.2 τ) ω)
  | .ustatisticMedian => fun ω =>
      intervalClipQ lo 1 (rawBlockMedianQ (fun r => spinStatisticQ M (List.ofFn r) τ) ω)

/-- Construction for consumed Correlation Records in the correlation execution model. -/
def consumedCorrelationRecords (mode : CorrelationMode) (n K : ℕ) :
    CorrelationData S mode n K → List (S × Bool) :=
  match mode with
  | .zero => fun _ => []
  | .matched => fun z => List.ofFn z.1 ++ List.ofFn z.2
  | .matchedMedian => fun ω =>
      (List.ofFn ω).flatMap (fun z => List.ofFn z.1 ++ List.ofFn z.2)
  | .ustatisticMedian => fun ω => (List.ofFn ω).flatMap List.ofFn

noncomputable section
variable [Fintype S] [Nonempty S]

/-- Construction for correlation Law in the correlation execution model. -/
def correlationLaw (mode : CorrelationMode) (n K : ℕ) (m : S → ℝ)
    (hm : ∀ x, |m x|≤1) : FinDist (CorrelationData S mode n K) :=
  match mode with
  | .zero =>
      { prob := fun _ => 1
        nonneg := fun _ => zero_le_one
        sum_one := by simp [CorrelationData] }
  | .matched => productLaw (cohortLaw (signedRecordLaw m hm) n)
      (cohortLaw (signedRecordLaw m hm) n)
  | .matchedMedian => cohortLaw
      (productLaw (cohortLaw (signedRecordLaw m hm) n) (cohortLaw (signedRecordLaw m hm) n)) K
  | .ustatisticMedian => cohortLaw (cohortLaw (signedRecordLaw m hm) n) K

omit [Fintype S] [Nonempty S] [DecidableEq S] in
/-- Complete original `consumed_correlation_records_length` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
theorem consumed_correlation_records_length (mode : CorrelationMode) (n K : ℕ)
    (ω : CorrelationData S mode n K) :
    (consumedCorrelationRecords mode n K ω).length =
      scheduledCopies ⟨mode,n,K,0,0,0⟩ := by
  cases mode <;> simp [consumedCorrelationRecords, scheduledCopies, List.length_flatMap,
    List.map_ofFn, List.sum_ofFn] <;> ring

omit [Fintype S] [Nonempty S] [DecidableEq S] in
/-- Complete original `planned_correlation_consumed_copies` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_correlation_consumed_copies (M : ℕ) (rootM ε ρ : ℚ)
    (ω : CorrelationData S (correlationPlanQ M rootM ε ρ).mode
      (correlationPlanQ M rootM ε ρ).records (correlationPlanQ M rootM ε ρ).blocks) :
    let p := correlationPlanQ M rootM ε ρ
    (consumedCorrelationRecords p.mode p.records p.blocks ω).length=p.copies := by
  dsimp only
  rw [correlation_plan_copy_account]
  exact consumed_correlation_records_length _ _ _ ω

/-- Complete original `finite_bad_clip` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
private theorem finite_bad_clip {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℚ) (lo : ℚ) (μ ε : ℝ)
    (hlo : (lo : ℝ)≤μ) (hhi : μ≤1) :
    finiteBadMass p (fun x => (intervalClipQ lo 1 (f x) : ℝ)) μ ε ≤
      finiteBadMass p (fun x => (f x : ℝ)) μ ε := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean]
  apply finite_expect_mono
  intro x
  have hc : |(intervalClipQ lo 1 (f x) : ℝ)-μ| ≤ |(f x : ℝ)-μ| := by
    simpa only [interval_clip_cast, Rat.cast_one] using
      interval_clip_contract (lo : ℝ) 1 (f x : ℝ) μ hlo hhi
  by_cases h : ε < |(intervalClipQ lo 1 (f x) : ℝ)-μ|
  · simp only [ite_eq_left h, ite_eq_left (lt_of_lt_of_le h hc), le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

omit [DecidableEq S] in
/-- Complete original `correlation_center_bound` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
private theorem correlation_center_bound (m : S → ℝ) (hm : ∀ x, |m x|≤1)
    (τ : S → S) : |siteMean (fun x => m x*m (τ x))|≤1 := by
  apply site_mean_abs_le_one
  intro x
  rw [abs_mul]
  exact (mul_le_mul (hm x) (hm (τ x)) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

/-- Complete original `planned_correlation_confidence` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_correlation_confidence (τ : Equiv.Perm S)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) (rootM ε ρ lo : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1)
    (hlo : (lo : ℝ)≤siteMean (fun x => m x*m (τ x))) :
    let p := correlationPlanQ (Fintype.card S) rootM ε ρ
    finiteBadMass (correlationLaw p.mode p.records p.blocks m hm)
      (fun ω => (correlationOutputQ p.mode p.records p.blocks (Fintype.card S) τ lo ω : ℝ))
      (siteMean (fun x => m x*m (τ x))) (ε : ℝ) ≤ (ρ : ℝ) := by
  have hcenter := correlation_center_bound m hm τ
  have hhi := (abs_le.mp hcenter).2
  dsimp only
  generalize hp : correlationPlanQ (Fintype.card S) rootM ε ρ = p
  dsimp only [correlationPlanQ] at hp
  split_ifs at hp with hzero hcount hx
  all_goals subst p
  · have hz : (1 : ℝ)≤ε := by exact_mod_cast hzero
    have he : ¬(ε : ℝ) < |((0 : ℚ) : ℝ)-siteMean (fun x => m x*m (τ x))| := by
      simpa only [Rat.cast_zero, zero_sub, abs_neg, not_lt] using hcenter.trans hz
    simp only [correlationLaw, correlationOutputQ, finiteBadMass, he,
      Finset.filter_false, Finset.sum_empty]
    exact (Rat.cast_pos.mpr hρ).le
  · have he1 : ε≤1 := (lt_of_not_ge hzero).le
    apply (finite_bad_clip _ _ lo _ _ hlo hhi).trans
    have ht := signed_planned_single_match_confidence τ m m hm hm ε ρ hε he1 hρ hρ1 hcount
    simp only [setAverage, siteMean, correlationLaw] at ht ⊢
    exact ht
  · have he1 : ε≤1 := (lt_of_not_ge hzero).le
    apply (finite_bad_clip _ _ lo _ _ hlo hhi).trans
    have ht := signed_planned_saturated_median_confidence τ m m hm hm ε ρ hε he1 hρ hx
    simp only [setAverage, siteMean, finiteBadMass, correlationLaw, cohortLaw,
      FinDist.probEvent] at ht ⊢
    exact ht
  · apply (finite_bad_clip _ _ lo _ _ hlo hhi).trans
    have ht := signed_planned_fallback_confidence τ m hm rootM ε ρ hroot hε hρ
    simp only [finiteBadMass, correlationLaw, cohortLaw, FinDist.probEvent] at ht ⊢
    exact ht

/-- Complete original `planned_spin_correlation_confidence` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_spin_correlation_confidence (τ : Equiv.Perm S)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) (rootM ε ρ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) :
    let p := correlationPlanQ (Fintype.card S) rootM ε ρ
    finiteBadMass (correlationLaw p.mode p.records p.blocks m hm)
      (fun ω => (correlationOutputQ p.mode p.records p.blocks (Fintype.card S) τ (-1) ω : ℝ))
      (siteMean (fun x => m x*m (τ x))) (ε : ℝ) ≤ (ρ : ℝ) := by
  apply planned_correlation_confidence τ m hm rootM ε ρ (-1) hroot hε hρ hρ1
  simpa only [Rat.cast_neg, Rat.cast_one] using
    (abs_le.mp (correlation_center_bound m hm τ)).1

/-- Complete original `planned_current_correlation_confidence` guarantee for `CorrelationExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_current_correlation_confidence
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) (rootM ε ρ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) :
    let p := correlationPlanQ (Fintype.card S) rootM ε ρ
    finiteBadMass (correlationLaw p.mode p.records p.blocks m hm)
      (fun ω => (correlationOutputQ p.mode p.records p.blocks (Fintype.card S) id 0 ω : ℝ))
      (siteMean (fun x => (m x)^2)) (ε : ℝ) ≤ (ρ : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ siteMean (fun x => m x*m ((Equiv.refl S) x)) := by
    simpa only [Rat.cast_zero, Equiv.refl_apply] using
      (site_mean_nonneg (fun x => m x*m x) (fun x => mul_self_nonneg (m x)))
  have ht := planned_correlation_confidence (Equiv.refl S) m hm rootM ε ρ 0
    hroot hε hρ hρ1 hlo
  simpa only [Equiv.refl_apply, Equiv.coe_refl, id_eq, ← sq] using ht

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.consumed_correlation_records_length
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_correlation_consumed_copies
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_correlation_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_spin_correlation_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_current_correlation_confidence
