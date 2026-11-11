/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedPlanArithmetic

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Correlation Plan

Correlation Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched

/-- Constructors for Correlation Mode in the correlation plan model. -/
inductive CorrelationMode where
  | zero | matched | matchedMedian | ustatisticMedian
  deriving DecidableEq, Repr

/-- Data and invariants for Correlation Plan Q in the correlation plan model. -/
structure CorrelationPlanQ where
  mode : CorrelationMode
  records : ℕ
  blocks : ℕ
  copies : ℕ
  tolerance : ℚ
  failureProbability : ℚ
  deriving Repr

/-- Validation is separate from scheduling, as in the Python public entry. -/
def correlationPlanQ (M : ℕ) (rootM ε ρ : ℚ) : CorrelationPlanQ :=
  if 1≤ε then ⟨.zero, 0, 0, 0, ε, ρ⟩ else
    let n := matchedCountQ M ε ρ
    if n≤M then ⟨.matched, n, 1, 2*n, ε, ρ⟩ else
      if 2048≤(M : ℚ)*ε^2 then
        let K := saturatedBlocksQ M ε ρ
        ⟨.matchedMedian, M, K, 2*M*K, ε, ρ⟩
      else
        let n := blockRecordsQ 1 rootM ε
        let K := medianBlocksQ ρ
        ⟨.ustatisticMedian, n, K, n*K, ε, ρ⟩

/-- Construction for checked Correlation Plan Q in the correlation plan model. -/
def checkedCorrelationPlanQ (M : ℕ) (rootM ε ρ : ℚ) : Option CorrelationPlanQ :=
  if 0<ε ∧ 0<ρ ∧ ρ<1 then some (correlationPlanQ M rootM ε ρ) else none

/-- Construction for grid Correlation Plan Q in the correlation plan model. -/
def gridCorrelationPlanQ (d r : ℕ) (ε ρ : ℚ) : Option CorrelationPlanQ :=
  checkedCorrelationPlanQ (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ) ε ρ

/-- Counts refer to exactly the cohorts consumed, including empty matches. -/
def scheduledCopies (p : CorrelationPlanQ) : ℕ :=
  match p.mode with
  | .zero => 0
  | .matched => 2*p.records
  | .matchedMedian => 2*p.records*p.blocks
  | .ustatisticMedian => p.records*p.blocks

noncomputable section
open scoped BigOperators
open Qatlib

/-- Complete original `correlation_plan_copy_account` guarantee for `CorrelationPlan`; all source hypotheses and output obligations are retained. -/
theorem correlation_plan_copy_account (M : ℕ) (rootM ε ρ : ℚ) :
    let p := correlationPlanQ M rootM ε ρ
    p.copies=scheduledCopies p := by
  dsimp only
  dsimp only [correlationPlanQ]
  split_ifs <;> rfl

/-- Complete original `correlation_plan_odd_blocks` guarantee for `CorrelationPlan`; all source hypotheses and output obligations are retained. -/
theorem correlation_plan_odd_blocks (M : ℕ) (rootM ε ρ : ℚ) :
    let p := correlationPlanQ M rootM ε ρ
    p.mode≠.zero → 0<p.blocks ∧ p.blocks%2=1 := by
  dsimp only
  dsimp only [correlationPlanQ]
  split_ifs
  · simp
  · simp
  · exact fun _ => ⟨saturated_blocks_pos _ _ _, saturated_blocks_odd _ _ _⟩
  · exact fun _ => ⟨median_blocks_pos _, median_blocks_odd _⟩

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_planned_fallback_confidence` guarantee for `CorrelationPlan`; all source hypotheses and output obligations are retained. -/
theorem signed_planned_fallback_confidence (τ : Equiv.Perm S)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) (rootM ε ρ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) :
    (cohortLaw (signedRecordLaw m hm) (blockRecordsQ 1 rootM ε)).probEvent
      (fun ω : Fin (medianBlocksQ ρ) → Fin (blockRecordsQ 1 rootM ε) → S × Bool =>
        (ε : ℝ) < |(rawBlockMedianQ
          (fun r => spinStatisticQ (Fintype.card S) (List.ofFn r) τ) ω : ℝ)-
          siteMean (fun x => m x*m (τ x))|) ≤ (ρ : ℝ) := by
  simp_rw [raw_block_median_cast, spin_statistic_cast]
  have hn := block_records_guards 1 rootM ε
  apply spin_streaming_median_confidence m hm τ (ε : ℝ) (ρ : ℝ) hn.1
    (Rat.cast_pos.mpr hε)
  · simpa using hn.2.1
  · exact block_records_sqrt_guard 1 rootM ε _ hε hroot
  · exact median_blocks_pos ρ
  · exact Rat.cast_pos.mpr hρ
  · exact median_blocks_budget ρ hρ

-- For current-square, identity-shift spinStatisticQ is exactly the literal
-- alpha=1,beta=0 velocity U-statistic, including self-pair subtraction.
omit [Nonempty S] in
/-- Complete original `current_fallback_statistic_eq` guarantee for `CorrelationPlan`; all source hypotheses and output obligations are retained. -/
theorem current_fallback_statistic_eq {n : ℕ} (r : Fin n → S × Bool) :
    velocityStatisticQ (Fintype.card S) (List.ofFn r) (fun _ => 0) 1 0 =
      spinStatisticQ (Fintype.card S) (List.ofFn r) id := by
  dsimp only [velocityStatisticQ, spinStatisticQ]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp [velocitySiteQ, spinSiteQ]
  ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_plan_copy_account
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_plan_odd_blocks
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_planned_fallback_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.current_fallback_statistic_eq
