/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Joint Amplify

Probability of an event may depend on both the constructor output and its subsequent readout; it is evaluated in the dependent joint law.
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
open Qatlib
open scoped BigOperators Classical
/-- Construction for indicator in the joint amplify model. -/
def indicator {X : Type} (C : X → Prop) [DecidablePred C] (x : X) : ℝ := if C x then 1 else 0

/-- The finite protocol identity or bound `indicator_variance` holds under exactly the displayed hypotheses. -/
private theorem indicator_variance {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C] :
    p.variance (indicator C)≤1/4 := by
  let μ := p.expect (indicator C)
  have hpoint (x : X) : p.prob x*(indicator C x-μ)^2=
      p.prob x*indicator C x-2*μ*(p.prob x*indicator C x)+μ^2*p.prob x := by
    dsimp [indicator]; split_ifs <;> ring
  have hv : p.variance (indicator C)=μ-μ^2 := by
    change (∑ x,p.prob x*(indicator C x-μ)^2)=_
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,p.sum_one]
    change μ-2*μ*μ+μ^2*1=μ-μ^2
    ring
  rw [hv]
  nlinarith [sq_nonneg (μ-1/2)]

/-- Probability of an event may depend on both the constructor output and
its subsequent readout; it is evaluated in the dependent joint law. -/
theorem joint_event_identity {D Z : Type} [Fintype D] [Fintype Z]
    (μ : FinDist D) (P : D → FinDist Z) (C : D × Z → Prop) [DecidablePred C] :
    (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ P).expect (indicator C)=
      ∑ d, μ.prob d*(∑ z∈Finset.univ.filter (fun z => C (d,z)),(P d).prob z) := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [indicator]
  split_ifs <;> simp

/-- The finite protocol identity or bound `joint_success` holds under exactly the displayed hypotheses. -/
theorem joint_success {D Z : Type} [Fintype D] [DecidableEq D] [Fintype Z]
    (μ : FinDist D) (P : D → FinDist Z) (C : D × Z → Prop) [DecidablePred C]
    (G : Finset D) (b g : ℝ) (hb : 0≤b)
    (hG : g≤∑ d∈G,μ.prob d)
    (hP : ∀ d∈G,b≤∑ z∈Finset.univ.filter (fun z => C (d,z)),(P d).prob z) :
    b*g≤(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ P).expect (indicator C) := by
  rw [joint_event_identity]
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun d => μ.prob d*(∑ z∈Finset.univ.filter (fun z => C (d,z)),(P d).prob z))
    (Finset.subset_univ G)
    (fun d _ _ => mul_nonneg (μ.nonneg d) (Finset.sum_nonneg (fun z _ => (P d).nonneg z)))
  calc
    b*g≤b*(∑ d∈G,μ.prob d) := mul_le_mul_of_nonneg_left hG hb
    _ = ∑ d∈G,μ.prob d*b := by rw [Finset.mul_sum]; congr 1; funext d; ring
    _ ≤ ∑ d∈G,μ.prob d*(∑ z∈Finset.univ.filter (fun z => C (d,z)),(P d).prob z) :=
      Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hP d hd) (μ.nonneg d))
    _ ≤ _ := hsub

/-- A 2/3-good constructor and BHMT readout have joint success at least 8/15,
without assuming that failed constructors produce a successful readout. -/
theorem constructor_ae_success {D Z : Type} [Fintype D] [DecidableEq D] [Fintype Z]
    (μ : FinDist D) (P : D → FinDist Z) (C : D × Z → Prop) [DecidablePred C]
    (G : Finset D) (hG : 2/3≤∑ d∈G,μ.prob d)
    (hP : ∀ d∈G,8/Real.pi^2≤∑ z∈Finset.univ.filter (fun z => C (d,z)),(P d).prob z) :
    8/15≤(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ P).expect (indicator C) := by
  have hpi : Real.pi^2≤10 := by nlinarith [Real.pi_pos,Real.pi_lt_d2]
  have hp : 4/5≤8/Real.pi^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  have hh := joint_success μ P C G (4/5) (2/3) (by norm_num) hG (fun d hd => hp.trans (hP d hd))
  norm_num at hh ⊢
  exact hh

/-- Independent reconstruction and readout, including failed constructors in
its one-shot law, amplify a success probability of at least 8/15. -/
theorem independent_majority_failure {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (C : X → Prop) [DecidablePred C]
    (hmean : 8/15≤p.expect (indicator C)) :
    p.probEvent (L := 1001) (fun ω => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω≤1/2)≤1/3 := by
  have htail := p.chebyshev_avg (indicator C) (by decide : 0<1001) (1/31) (by norm_num)
  have hsub : Finset.univ.filter (fun ω : Fin 1001 → X => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω≤1/2)⊆
      Finset.univ.filter (fun ω : Fin 1001 → X => 1/31 < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω-p.expect (indicator C)|) := by
    intro ω hω
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hω ⊢
    have hh := neg_le_abs (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω-p.expect (indicator C))
    linarith
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun ω : Fin 1001 → X => p.probOf ω) hsub
    (fun ω _ _ => Finset.prod_nonneg (fun i _ => p.nonneg (ω i)))
  change p.probEvent (fun ω : Fin 1001 → X => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (indicator C) ω≤1/2)≤_ at hs
  have hv := indicator_variance p C
  have hp : (0 : ℝ)<1001*(1/31)^2 := by norm_num
  have hdiv := (div_le_div_iff_of_pos_right hp).mpr hv
  have hh := hs.trans htail
  exact hh.trans (hdiv.trans (by norm_num))



end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
