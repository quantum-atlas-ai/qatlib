/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.BoundedAveragePlan
import Qatlib.Concepts.SpinorSampling.Matching.TargetNormPlan
import Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidualExecution

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Linear Target Execution

Linear Target Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual

variable {S : Type} [DecidableEq S]

/-- Construction for cross Record Value Q in the linear target execution model. -/
def crossRecordValueQ (u : S → ℚ) (α β : ℚ) (z : S × Bool) : ℚ :=
  -2*α*β*u z.1*(recordSignZ z.2 : ℚ)

/-- Construction for cross Target Output Q in the linear target execution model. -/
def crossTargetOutputQ {n : ℕ} (u : S → ℚ) (α β : ℚ) (ω : Fin n → S × Bool) : ℚ :=
  2*splitLinearQ (List.ofFn ω) u α β

/-- Construction for cross Target Queries in the linear target execution model. -/
def crossTargetQueries {n : ℕ} (ω : Fin n → S × Bool) : List S :=
  (collectRecordCounts (List.ofFn ω)).keys

noncomputable section
variable [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] [DecidableEq S] in
/-- Complete original `cross_record_value_cast` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_record_value_cast (u : S → ℚ) (α β : ℚ) (z : S × Bool) :
    (crossRecordValueQ u α β z : ℝ)=
      -2*(α : ℝ)*(β : ℝ)*(u z.1 : ℝ)*recordSign z.2 := by
  simp only [crossRecordValueQ, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_intCast,
    record_sign_cast]

omit [Nonempty S] in
/-- Complete original `cross_output_average_cast` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_output_average_cast {n : ℕ} (u : S → ℚ) (α β : ℚ)
    (ω : Fin n → S × Bool) :
    (crossTargetOutputQ u α β ω : ℝ)=
      FinDist.avg (fun z => (crossRecordValueQ u α β z : ℝ)) ω := by
  rw [crossTargetOutputQ, Rat.cast_mul, Rat.cast_ofNat, split_linear_cast]
  simp only [FinDist.avg, cross_record_value_cast, targetLinear]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq S] in
/-- Complete original `cross_record_mean` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_record_mean (u : S → ℚ) (α β : ℚ) (m : S → ℝ) (hm : ∀ x, |m x|≤1) :
    (signedRecordLaw m hm).expect (fun z => (crossRecordValueQ u α β z : ℝ))=
      -2*(α : ℝ)*(β : ℝ)*siteMean (fun x => m x*(u x : ℝ)) := by
  have he : (fun z => (crossRecordValueQ u α β z : ℝ)) =
      fun z : S × Bool => recordSign z.2*(-2*(α : ℝ)*(β : ℝ)*(u z.1 : ℝ)) := by
    funext z
    rw [cross_record_value_cast]
    ring
  rw [he, signed_weighted_sign_expect m (fun x => -2*(α : ℝ)*(β : ℝ)*(u x : ℝ)) hm]
  unfold siteMean
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype S] [Nonempty S] [DecidableEq S] in
/-- Complete original `cross_record_abs_bound` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_record_abs_bound (u : S → ℚ) (α β U : ℚ)
    (hα : 0≤α) (hβ : 0≤β) (hu : ∀ x, |u x|≤U) (z : S × Bool) :
    |crossRecordValueQ u α β z|≤2*α*β*U := by
  have hs : |(recordSignZ z.2 : ℚ)|=1 := by cases z.2 <;> norm_num [recordSignZ]
  calc
    _ = 2*α*β*|u z.1| := by
      simp only [crossRecordValueQ,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0 : ℚ)≤2),abs_of_nonneg hα,
        abs_of_nonneg hβ,hs,mul_one]
    _ ≤ 2*α*β*U := mul_le_mul_of_nonneg_left (hu z.1) (by positivity)

/-- Complete original `planned_cross_target_confidence` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_cross_target_confidence (u : S → ℚ) (α β U ε ρ : ℚ)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) (hα : 0≤α) (hβ : 0≤β) (hU : 0≤U)
    (hu : ∀ x, |u x|≤U) (hε : 0<ε) (hρ : 0<ρ) :
    finiteBadMass (cohortLaw (signedRecordLaw m hm) (linearCountQ (2*α*β*U) ε ρ))
      (fun ω => (crossTargetOutputQ u α β ω : ℝ))
      (-2*(α : ℝ)*(β : ℝ)*siteMean (fun x => m x*(u x : ℝ))) (ε : ℝ)≤(ρ : ℝ) := by
  have ht := planned_bounded_average_confidence (signedRecordLaw m hm)
    (crossRecordValueQ u α β) (2*α*β*U) ε ρ (by positivity) hε hρ
    (cross_record_abs_bound u α β U hα hβ hu)
  rw [cross_record_mean] at ht
  simp_rw [bounded_average_cast] at ht
  simpa only [cross_output_average_cast] using ht

omit [Nonempty S] in
/-- Complete original `cross_target_queries_bound` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_target_queries_bound {n : ℕ} (ω : Fin n → S × Bool) :
    (crossTargetQueries ω).length≤min n (Fintype.card S) := by
  apply le_min
  · exact record_counts_query_quota ω
  · dsimp only [crossTargetQueries]
    rw [← List.toFinset_card_of_nodup (collectRecordCounts (List.ofFn ω)).keys_nodup]
    exact Finset.card_le_univ _

/-- Complete original `planned_squared_target_norm_confidence` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem planned_squared_target_norm_confidence (u : S → ℚ) (β U ε ρ : ℚ)
    (hβ : 0≤β) (hu : ∀ x, |u x|≤U) (hε : 0<ε) (hρ : 0<ρ) :
    let p := targetNormPlanQ (Fintype.card S) (β*U) ε ρ
    finiteBadMass (targetNormLaw p.mode p.records p.blocks)
      (fun ω => (targetNormOutputQ p.mode p.records p.blocks (fun x => (β*u x)^2) ω : ℝ))
      (targetSquare (β : ℝ) (fun x => (u x : ℝ))) (ε : ℝ)≤(ρ : ℝ) := by
  have hf (x : S) : (0 : ℚ)≤(β*u x)^2 ∧ (β*u x)^2≤(β*U)^2 := by
    constructor
    · positivity
    · have ha : |β*u x|≤β*U := by
        rw [abs_mul,abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (hu x) hβ
      have hs := pow_le_pow_left₀ (abs_nonneg (β*u x)) ha 2
      simpa only [sq_abs] using hs
  have ht := planned_target_norm_confidence (fun x => (β*u x)^2) (β*U) ε ρ hε hρ hf
  simpa only [siteMean,targetSquare,Rat.cast_mul,Rat.cast_pow] using ht

omit [Fintype S] [Nonempty S] in
/-- Complete original `cross_output_uses_queries` guarantee for `LinearTargetExecution`; all source hypotheses and output obligations are retained. -/
theorem cross_output_uses_queries {n : ℕ} (ω : Fin n → S × Bool)
    (u v : S → ℚ) (α β : ℚ) (h : ∀ x ∈ crossTargetQueries ω, u x=v x) :
    crossTargetOutputQ u α β ω=crossTargetOutputQ v α β ω := by
  dsimp only [crossTargetOutputQ,splitLinearQ]
  congr 2
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  simp only [splitLinearSiteQ,h x hx]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_record_value_cast
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_output_average_cast
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_record_mean
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_record_abs_bound
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_cross_target_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_target_queries_bound
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_squared_target_norm_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.cross_output_uses_queries
