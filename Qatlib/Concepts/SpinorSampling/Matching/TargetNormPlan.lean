/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.BoundedAveragePlan
import Mathlib.Data.Finset.Sort

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Target Norm Plan

Target Norm Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Constructors for Target Norm Mode in the target norm plan model. -/
inductive TargetNormMode where
  | zero | exact | sampled
  deriving DecidableEq, Repr

/-- Data and invariants for Target Norm Plan Q in the target norm plan model. -/
structure TargetNormPlanQ where
  mode : TargetNormMode
  records : ℕ
  blocks : ℕ
  queries : ℕ
  deriving Repr

/-- Construction for norm Count Q in the target norm plan model. -/
def normCountQ (B ε : ℚ) : ℕ := ceilNatQ (max 1 (16*B^4/ε^2))

/-- Construction for target Norm Plan Q in the target norm plan model. -/
def targetNormPlanQ (M : ℕ) (B ε ρ : ℚ) : TargetNormPlanQ :=
  if B=0 then ⟨.zero,0,0,0⟩ else
    let n := normCountQ B ε
    let K := medianBlocksQ ρ
    if M≤n*K then ⟨.exact,M,1,M⟩ else ⟨.sampled,n,K,n*K⟩

/-- Construction for Target Norm Data in the target norm plan model. -/
def TargetNormData (S : Type) (mode : TargetNormMode) (n K : ℕ) : Type :=
  match mode with
  | .zero | .exact => Unit
  | .sampled => Fin K → Fin n → S

instance {S : Type} [Fintype S] (mode : TargetNormMode) (n K : ℕ) :
    Fintype (TargetNormData S mode n K) := by
  cases mode <;> dsimp only [TargetNormData] <;> infer_instance

instance {S : Type} [DecidableEq S] (mode : TargetNormMode) (n K : ℕ) :
    DecidableEq (TargetNormData S mode n K) := by
  cases mode <;> dsimp only [TargetNormData] <;> infer_instance

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for target Norm Output Q in the target norm plan model. -/
def targetNormOutputQ (mode : TargetNormMode) (n K : ℕ) (f : S → ℚ) :
    TargetNormData S mode n K → ℚ :=
  match mode with
  | .zero => fun _ => 0
  | .exact => fun _ => (∑ x : S, f x)/(Fintype.card S : ℚ)
  | .sampled => fun ω => rawBlockMedianQ (boundedAverageQ f) ω

/-- Construction for target Norm Queries in the target norm plan model. -/
def targetNormQueries [LinearOrder S] (mode : TargetNormMode) (n K : ℕ) :
    TargetNormData S mode n K → List S :=
  match mode with
  | .zero => fun _ => []
  | .exact => fun _ => Finset.univ.sort (· ≤ ·)
  | .sampled => fun ω => (List.ofFn ω).flatMap List.ofFn

noncomputable section

/-- Construction for target Norm Law in the target norm plan model. -/
def targetNormLaw (mode : TargetNormMode) (n K : ℕ) : FinDist (TargetNormData S mode n K) :=
  match mode with
  | .zero | .exact =>
      { prob := fun _ => 1
        nonneg := fun _ => zero_le_one
        sum_one := by simp [TargetNormData] }
  | .sampled => cohortLaw (cohortLaw (uniformLaw S) n) K

omit [DecidableEq S] in
/-- Complete original `uniform_expect_site_mean` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem uniform_expect_site_mean (f : S → ℝ) :
    (uniformLaw S).expect f=siteMean f := by
  simp only [FinDist.expect, uniformLaw, siteMean, one_div_mul_eq_div, ← Finset.sum_div]

/-- Complete original `norm_count_guards` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem norm_count_guards (B ε : ℚ) :
    1≤normCountQ B ε ∧ 16*(B : ℝ)^4/(ε : ℝ)^2≤(normCountQ B ε : ℝ) := by
  let q := max 1 (16*B^4/ε^2)
  have hq : (0 : ℚ)≤q := (by norm_num : (0 : ℚ)≤1).trans (le_max_left _ _)
  have hc := (ceil_nat_bounds q hq).1
  have h1 : (1 : ℝ)≤ceilNatQ q := by
    have hh : (1 : ℚ)≤q := le_max_left _ _
    exact (show (1 : ℝ)≤q by exact_mod_cast hh).trans hc
  have hB : 16*(B : ℝ)^4/(ε : ℝ)^2≤(q : ℝ) := by
    exact_mod_cast (show 16*B^4/ε^2≤q from le_max_right _ _)
  exact ⟨by exact_mod_cast h1, hB.trans hc⟩

/-- Complete original `planned_norm_median_confidence` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem planned_norm_median_confidence {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℚ) (B ε ρ : ℚ) (hε : 0<ε) (hρ : 0<ρ)
    (hf : ∀ x, |f x|≤B^2) :
    (cohortLaw p (normCountQ B ε)).probEvent
      (fun ω : Fin (medianBlocksQ ρ) → Fin (normCountQ B ε) → X =>
        (ε : ℝ) < |(rawBlockMedianQ (boundedAverageQ f) ω : ℝ)-
          p.expect (fun x => (f x : ℝ))|) ≤ (ρ : ℝ) := by
  simp_rw [raw_block_median_cast, bounded_average_cast]
  obtain ⟨hn1,hnB⟩ := norm_count_guards B ε
  have hn : 0<normCountQ B ε := by omega
  have hεR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hε2 := sq_pos_of_pos hεR
  have hv : p.variance (fun x => (f x : ℝ))≤(B : ℝ)^4 := by
    apply (finite_variance_le_second _ _).trans
    calc
      _ ≤ p.expect (fun _ => (B : ℝ)^4) := by
        apply finite_expect_mono
        intro x
        have hh : |(f x : ℝ)|≤(B : ℝ)^2 := by exact_mod_cast hf x
        have hs := pow_le_pow_left₀ (abs_nonneg (f x : ℝ)) hh 2
        rw [sq_abs] at hs
        nlinarith only [hs]
      _ = _ := finite_expect_const _ _
  have hb := (div_le_iff₀ hε2).mp hnB
  have hden : (0 : ℝ)<(normCountQ B ε : ℝ)*(ε : ℝ)^2 := by positivity
  have hblock : finiteBadMass (cohortLaw p (normCountQ B ε))
      (FinDist.avg (fun x => (f x : ℝ))) (p.expect (fun x => (f x : ℝ))) (ε : ℝ)≤3/16 := by
    have ht := p.chebyshev_avg (fun x => (f x : ℝ)) hn (ε : ℝ) hεR
    have hfinal : p.variance (fun x => (f x : ℝ))/
        ((normCountQ B ε : ℝ)*(ε : ℝ)^2)≤3/16 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hv,hb,hden]
    exact ht.trans hfinal
  exact finite_median_confidence _ _ _ _ (ρ : ℝ) (median_blocks_pos ρ)
    (Rat.cast_pos.mpr hρ) hblock (median_blocks_budget ρ hρ)

/-- Complete original `target_norm_plan_queries` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem target_norm_plan_queries (M : ℕ) (B ε ρ : ℚ) :
    (targetNormPlanQ M B ε ρ).queries =
      if B=0 then 0 else min M (normCountQ B ε*medianBlocksQ ρ) := by
  dsimp only [targetNormPlanQ]
  split_ifs with hz hscan
  · rfl
  · exact (min_eq_left hscan).symm
  · exact (min_eq_right (lt_of_not_ge hscan).le).symm

omit [Nonempty S] [DecidableEq S] in
/-- Complete original `planned_norm_queries_length` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem planned_norm_queries_length [LinearOrder S] (B ε ρ : ℚ)
    (ω : TargetNormData S (targetNormPlanQ (Fintype.card S) B ε ρ).mode
      (targetNormPlanQ (Fintype.card S) B ε ρ).records
      (targetNormPlanQ (Fintype.card S) B ε ρ).blocks) :
    let p := targetNormPlanQ (Fintype.card S) B ε ρ
    (targetNormQueries p.mode p.records p.blocks ω).length=p.queries := by
  dsimp only
  generalize hp : targetNormPlanQ (Fintype.card S) B ε ρ=p at ω ⊢
  dsimp only [targetNormPlanQ] at hp
  split_ifs at hp with hz hscan
  all_goals subst p
  all_goals simp [targetNormQueries, List.length_flatMap, List.map_ofFn, List.sum_ofFn]
  ring

/-- Complete original `planned_target_norm_confidence` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem planned_target_norm_confidence (f : S → ℚ) (B ε ρ : ℚ)
    (hε : 0<ε) (hρ : 0<ρ) (hf : ∀ x, 0≤f x ∧ f x≤B^2) :
    let p := targetNormPlanQ (Fintype.card S) B ε ρ
    finiteBadMass (targetNormLaw p.mode p.records p.blocks)
      (fun ω => (targetNormOutputQ p.mode p.records p.blocks f ω : ℝ))
      (siteMean (fun x => (f x : ℝ))) (ε : ℝ)≤(ρ : ℝ) := by
  dsimp only
  generalize hp : targetNormPlanQ (Fintype.card S) B ε ρ=p
  dsimp only [targetNormPlanQ] at hp
  split_ifs at hp with hz hscan
  all_goals subst p
  · have hf0 (x : S) : f x=0 := by have hh := hf x; rw [hz] at hh; norm_num at hh; linarith
    have hcenter : siteMean (fun x => (f x : ℝ))=0 := by simp [siteMean,hf0]
    simp [targetNormLaw,targetNormOutputQ,finiteBadMass,hcenter,not_lt_of_ge
      (Rat.cast_nonneg.mpr hε.le)]
    exact (Rat.cast_pos.mpr hρ).le
  · have houtput (ω : Unit) : (targetNormOutputQ .exact (Fintype.card S) 1 f ω : ℝ)=
        siteMean (fun x => (f x : ℝ)) := by
      simp only [targetNormOutputQ,siteMean,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
    have hnot (ω : Unit) : ¬(ε : ℝ) <
        |(targetNormOutputQ .exact (Fintype.card S) 1 f ω : ℝ)-siteMean (fun x => (f x : ℝ))| := by
      rw [houtput, sub_self, abs_zero]
      exact not_lt_of_ge (Rat.cast_nonneg.mpr hε.le)
    simp only [finiteBadMass,hnot,Finset.filter_false,Finset.sum_empty]
    exact (Rat.cast_pos.mpr hρ).le
  · have habs (x : S) : |f x|≤B^2 := by rw [abs_of_nonneg (hf x).1]; exact (hf x).2
    have ht := planned_norm_median_confidence (uniformLaw S) f B ε ρ hε hρ habs
    rw [uniform_expect_site_mean] at ht
    exact ht

omit [Nonempty S] [DecidableEq S] in
/-- Complete original `target_norm_exact_query_value` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem target_norm_exact_query_value [LinearOrder S] (f : S → ℚ) (n K : ℕ)
    (ω : TargetNormData S .exact n K) :
    targetNormOutputQ .exact n K f ω=
      ((targetNormQueries .exact n K ω).map f).sum/(Fintype.card S : ℚ) := by
  dsimp only [targetNormOutputQ,targetNormQueries]
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _),Finset.sort_toFinset]

omit [Nonempty S] [DecidableEq S] in
/-- Complete original `target_norm_output_uses_queries` guarantee for `TargetNormPlan`; all source hypotheses and output obligations are retained. -/
theorem target_norm_output_uses_queries [LinearOrder S] (mode : TargetNormMode) (n K : ℕ)
    (ω : TargetNormData S mode n K) (f g : S → ℚ)
    (h : ∀ x ∈ targetNormQueries mode n K ω, f x=g x) :
    targetNormOutputQ mode n K f ω=targetNormOutputQ mode n K g ω := by
  cases mode with
  | zero => rfl
  | exact =>
      rw [target_norm_exact_query_value,target_norm_exact_query_value]
      congr 2
      apply List.map_congr_left
      exact h
  | sampled =>
      have he (i : Fin K) : boundedAverageQ f (ω i)=boundedAverageQ g (ω i) := by
        unfold boundedAverageQ
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        apply h
        exact List.mem_flatMap.mpr ⟨ω i,List.mem_ofFn.mpr ⟨i,rfl⟩,
          List.mem_ofFn.mpr ⟨j,rfl⟩⟩
      dsimp only [targetNormOutputQ,rawBlockMedianQ]
      congr 1
      funext i
      exact he i

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_expect_site_mean
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.norm_count_guards
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_norm_median_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.target_norm_plan_queries
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_norm_queries_length
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_target_norm_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.target_norm_exact_query_value
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.target_norm_output_uses_queries
