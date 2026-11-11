/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.HighConfidenceExecution

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# High Confidence Accounting

High Confidence Accounting constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Data and invariants for High Confidence Receipt Q in the high confidence accounting model. -/
structure HighConfidenceReceiptQ where
  value : ℚ
  copies : ℕ
  targetQueries : ℕ
  uniformSites : ℕ
  deriving Repr

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Construction for high Velocity Records in the high confidence accounting model. -/
def highVelocityRecords {d : ℕ} (p : HighConfidencePlanQ) (z : HighConfidenceData S d p)
    (j : Fin d) : List (S × Bool) :=
  consumedCorrelationRecords p.current.mode p.current.records p.current.blocks (z.1 j).1 ++
    List.ofFn (z.1 j).2.1

/-- Construction for high Spin Records in the high confidence accounting model. -/
def highSpinRecords {d : ℕ} (p : HighConfidencePlanQ) (z : HighConfidenceData S d p)
    (i : Fin 3 × Fin d) : List (S × Bool) :=
  consumedCorrelationRecords p.spinSchedule.mode p.spinSchedule.records p.spinSchedule.blocks (z.2 i)

/-- Construction for high Target Queries in the high confidence accounting model. -/
def highTargetQueries [LinearOrder S] {d : ℕ} (p : HighConfidencePlanQ)
    (z : HighConfidenceData S d p) (j : Fin d) : List S :=
  crossTargetQueries (z.1 j).2.1 ++
    targetNormQueries p.norm.mode p.norm.records p.norm.blocks (z.1 j).2.2

/-- Construction for execute High Confidence Q in the high confidence accounting model. -/
def executeHighConfidenceQ [LinearOrder S] {d : ℕ} (p : HighConfidencePlanQ)
    (u : Fin d → S → ℚ) (e : Fin d → S → S) (α β U γ : ℚ)
    (z : HighConfidenceData S d p) : HighConfidenceReceiptQ :=
  { value := highConfidenceOutputQ p u e α β U γ z
    copies := (∑ j : Fin d, (highVelocityRecords p z j).length)+
      (∑ i : Fin 3 × Fin d, (highSpinRecords p z i).length)
    targetQueries := ∑ j : Fin d, (highTargetQueries p z j).length
    uniformSites := if p.norm.mode=.sampled then
      ∑ j : Fin d, (targetNormQueries p.norm.mode p.norm.records p.norm.blocks (z.1 j).2.2).length
      else 0 }

noncomputable section

omit [Fintype S] [DecidableEq S] in
/-- Complete original `correlation_records_length_schedule` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem correlation_records_length_schedule (p : CorrelationPlanQ)
    (z : CorrelationData S p.mode p.records p.blocks) :
    (consumedCorrelationRecords p.mode p.records p.blocks z).length=scheduledCopies p := by
  simpa only [scheduledCopies] using consumed_correlation_records_length p.mode p.records p.blocks z

/-- Complete original `high_plan_current_schedule_account` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem high_plan_current_schedule_account (d M : ℕ) (rootM α β U γ η δ : ℚ) :
    let p := highConfidencePlanQ d M rootM α β U γ η δ
    scheduledCopies p.current=p.current.copies :=
  (correlation_plan_copy_account M rootM ((η/(8*(d : ℚ)))/α^2) (δ/(4*(d : ℚ)))).symm

/-- Complete original `high_plan_spin_schedule_account` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem high_plan_spin_schedule_account (d M : ℕ) (rootM α β U γ η δ : ℚ) :
    let p := highConfidencePlanQ d M rootM α β U γ η δ
    scheduledCopies p.spinSchedule=p.spinSchedule.copies := by
  dsimp only
  by_cases hγ : γ=0
  · simp [highConfidencePlanQ,hγ,HighConfidencePlanQ.spinSchedule,scheduledCopies]
  · rw [high_plan_spin_fields d M rootM α β U γ η δ hγ]
    exact (correlation_plan_copy_account M rootM (η/(24*(d : ℚ)*γ)) (δ/(12*(d : ℚ)))).symm

/-- Complete original `executed_high_confidence_copies` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_high_confidence_copies [LinearOrder S] (d : ℕ)
    (rootM α β U γ η δ : ℚ)
    (u : Fin d → S → ℚ) (e : Fin d → S → S)
    (z : HighConfidenceData S d (highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ)) :
    let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
    (executeHighConfidenceQ p u e α β U γ z).copies=p.copies := by
  let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
  have hC := high_plan_current_schedule_account d (Fintype.card S) rootM α β U γ η δ
  have hS := high_plan_spin_schedule_account d (Fintype.card S) rootM α β U γ η δ
  have hv (j : Fin d) : (highVelocityRecords p z j).length=p.current.copies+p.crossRecords := by
    rw [highVelocityRecords,List.length_append,correlation_records_length_schedule,List.length_ofFn]
    rw [hC]
  have hs (i : Fin 3 × Fin d) : (highSpinRecords p z i).length=p.spinSchedule.copies := by
    rw [highSpinRecords,correlation_records_length_schedule,hS]
  change (∑ j : Fin d, (highVelocityRecords p z j).length)+
    (∑ i : Fin 3 × Fin d, (highSpinRecords p z i).length)=p.copies
  simp_rw [hv,hs]
  rw [show p.copies=d*(p.current.copies+p.crossRecords)+3*d*p.spinSchedule.copies from
    (high_plan_accounts d (Fintype.card S) rootM α β U γ η δ).1]
  simp

/-- Complete original `executed_high_confidence_query_bound` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_high_confidence_query_bound [LinearOrder S] (d : ℕ)
    (rootM α β U γ η δ : ℚ)
    (u : Fin d → S → ℚ) (e : Fin d → S → S)
    (z : HighConfidenceData S d (highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ)) :
    let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
    (executeHighConfidenceQ p u e α β U γ z).targetQueries≤p.targetQueries := by
  let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
  have hN (j : Fin d) :
      (targetNormQueries p.norm.mode p.norm.records p.norm.blocks (z.1 j).2.2).length=p.norm.queries := by
    exact planned_norm_queries_length (β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) (z.1 j).2.2
  have hQ (j : Fin d) : (highTargetQueries p z j).length≤min p.crossRecords (Fintype.card S)+p.norm.queries := by
    rw [highTargetQueries,List.length_append,hN]
    exact Nat.add_le_add_right (cross_target_queries_bound (z.1 j).2.1) _
  change (∑ j : Fin d, (highTargetQueries p z j).length)≤p.targetQueries
  calc
    _ ≤ ∑ _j : Fin d, (min p.crossRecords (Fintype.card S)+p.norm.queries) := Finset.sum_le_sum (fun j _ => hQ j)
    _ = _ := by
      rw [show p.targetQueries=d*min p.crossRecords (Fintype.card S)+d*p.norm.queries from
        (high_plan_accounts d (Fintype.card S) rootM α β U γ η δ).2]
      simp [Nat.mul_add]

/-- Complete original `executed_high_confidence_uniform_sites` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_high_confidence_uniform_sites [LinearOrder S] (d : ℕ)
    (rootM α β U γ η δ : ℚ)
    (u : Fin d → S → ℚ) (e : Fin d → S → S)
    (z : HighConfidenceData S d (highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ)) :
    let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
    (executeHighConfidenceQ p u e α β U γ z).uniformSites=
      if p.norm.mode=.sampled then d*p.norm.queries else 0 := by
  let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
  have hN (j : Fin d) :
      (targetNormQueries p.norm.mode p.norm.records p.norm.blocks (z.1 j).2.2).length=p.norm.queries := by
    exact planned_norm_queries_length (β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) (z.1 j).2.2
  change (if p.norm.mode=.sampled then
    ∑ j : Fin d, (targetNormQueries p.norm.mode p.norm.records p.norm.blocks (z.1 j).2.2).length else 0)=
    (if p.norm.mode=.sampled then d*p.norm.queries else 0)
  simp_rw [hN]
  simp


/-- Complete original `executed_high_confidence_accuracy` guarantee for `HighConfidenceAccounting`; all source hypotheses and output obligations are retained. -/
theorem executed_high_confidence_accuracy [LinearOrder S] [Nonempty S] {d : ℕ} (hd : 0<d)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (ms : Fin 3 → S → ℝ) (hs : ∀ x, ∑ a : Fin 3, (ms a x)^2=1)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (rootM α β U γ η δ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hα : 0<α) (hβ : 0≤β) (hU : 0≤U) (hγ : 0≤γ)
    (hu : ∀ j x, |u j x|≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1) :
    let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
    finiteBadMass (highConfidenceLaw p mv hmv ms (fun i x => unit_spin_component_bound ms hs i x))
      (fun z => ((executeHighConfidenceQ p u (fun j => e j) α β U γ z).value : ℝ))
      (implementedResidualLoss mv (fun j x => (u j x : ℝ)) ms e
        (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)≤(δ : ℝ) :=
  high_confidence_accuracy hd mv hmv ms hs u e rootM α β U γ η δ
    hroot hα hβ hU hγ hu hη hδ hδ1

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_records_length_schedule
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_current_schedule_account
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_spin_schedule_account
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.executed_high_confidence_copies
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.executed_high_confidence_query_bound
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.executed_high_confidence_uniform_sites

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.executed_high_confidence_accuracy
