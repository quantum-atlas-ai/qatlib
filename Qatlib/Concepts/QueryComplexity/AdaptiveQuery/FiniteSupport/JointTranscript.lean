/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
/-! Finite-law stages of the hidden-parameter/support-transcript argument.
Conditional distances control the JOINT law. No per-query hybrid bound or
operational outside-hit equality is supplied by these algebraic lemmas. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
open Qatlib
open scoped BigOperators Classical

/-- Construction for variation in the joint transcript model. -/
private def variation {X : Type} [Fintype X] (p q : FinDist X) : ℝ :=
  (∑ x, |p.prob x-q.prob x|)/2

/-- Construction for event in the joint transcript model. -/
private def event {X : Type} [Fintype X] (p : FinDist X) (E : Finset X) : ℝ := ∑ x∈E,p.prob x

/-- The finite protocol identity or bound `event_difference` holds under exactly the displayed hypotheses. -/
private theorem event_difference {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (E : Finset X) : |event p E-event q E|≤variation p q := by
  let d := fun x => p.prob x-q.prob x
  have hz : (∑ x,d x)=0 := by dsimp [d]; rw [Finset.sum_sub_distrib,p.sum_one,q.sum_one]; ring
  have hsplit := Finset.sum_add_sum_compl (s := E) (f := d)
  rw [hz] at hsplit
  have hc : (∑ x∈Eᶜ,d x)=-(∑ x∈E,d x) := by linarith
  have h1 := Finset.abs_sum_le_sum_abs d E
  have h2 := Finset.abs_sum_le_sum_abs d Eᶜ
  rw [hc,abs_neg] at h2
  have habs := Finset.sum_add_sum_compl (s := E) (f := fun x => |d x|)
  change |(∑ x∈E,p.prob x)-(∑ x∈E,q.prob x)|≤(∑ x,|d x|)/2
  rw [←Finset.sum_sub_distrib]
  change |∑ x∈E,d x|≤_
  linarith

/-- Analysis-only joint law: hidden parameters are retained together with the
whole transcript. It does not expose that register to an algorithm. -/
def jointLaw {H T : Type} [Fintype H] [Fintype T]
    (μ : FinDist H) (P : H → FinDist T) : FinDist (H × T) where
  prob ht := μ.prob ht.1*(P ht.1).prob ht.2
  nonneg ht := mul_nonneg (μ.nonneg _) ((P _).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum,(P _).sum_one,mul_one]
    exact μ.sum_one

/-- The finite protocol identity or bound `joint_variation_identity` holds under exactly the displayed hypotheses. -/
theorem joint_variation_identity {H T : Type} [Fintype H] [Fintype T]
    (μ : FinDist H) (P Q : H → FinDist T) :
    (∑ ht : H × T, |(jointLaw μ P).prob ht-(jointLaw μ Q).prob ht|)/2=
      ∑ h, μ.prob h*((∑ t, |(P h).prob t-(Q h).prob t|)/2) := by
  have hpoint (h : H) (t : T) : |μ.prob h*(P h).prob t-μ.prob h*(Q h).prob t|=
      μ.prob h*|(P h).prob t-(Q h).prob t| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (μ.nonneg h)]
  change (∑ ht : H × T, |μ.prob ht.1*(P ht.1).prob ht.2-μ.prob ht.1*(Q ht.1).prob ht.2|)/2=_
  rw [Fintype.sum_prod_type]
  simp_rw [hpoint,←Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The finite protocol identity or bound `hidden_event_transfer` holds under exactly the displayed hypotheses. -/
theorem hidden_event_transfer {H T : Type} [Fintype H] [DecidableEq H]
    [Fintype T] [DecidableEq T] (μ : FinDist H) (P Q : H → FinDist T)
    (E : Finset (H × T)) (δ : ℝ)
    (hconditional : (∑ h, μ.prob h*((∑ t, |(P h).prob t-(Q h).prob t|)/2))≤δ) :
    (∑ ht∈E,(jointLaw μ P).prob ht)≤(∑ ht∈E,(jointLaw μ Q).prob ht)+δ := by
  have hh := event_difference (jointLaw μ P) (jointLaw μ Q) E
  unfold variation at hh
  rw [joint_variation_identity] at hh
  have hd := (le_abs_self (event (jointLaw μ P) E-event (jointLaw μ Q) E)).trans (hh.trans hconditional)
  dsimp [event] at hd
  linarith

/-- The finite protocol identity or bound `first_hit_variation` holds under exactly the displayed hypotheses. -/
theorem first_hit_variation {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (E : Finset X) (hnohit : ∀ x∉E,p.prob x=q.prob x) :
    (∑ x,|p.prob x-q.prob x|)/2≤∑ x∈E,q.prob x := by
  have hcomp : (∑ x∈Eᶜ,p.prob x)=(∑ x∈Eᶜ,q.prob x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hnohit x (by simpa using hx)
  have hp := Finset.sum_add_sum_compl (s := E) (f := p.prob)
  have hq := Finset.sum_add_sum_compl (s := E) (f := q.prob)
  rw [p.sum_one] at hp
  rw [q.sum_one] at hq
  have hmass : (∑ x∈E,p.prob x)=(∑ x∈E,q.prob x) := by linarith
  have hzero : (∑ x∈Eᶜ,|p.prob x-q.prob x|)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hnohit x (by simpa using hx),sub_self,abs_zero]
  have hsplit := Finset.sum_add_sum_compl (s := E) (f := fun x => |p.prob x-q.prob x|)
  rw [hzero,add_zero] at hsplit
  have hs : (∑ x∈E,|p.prob x-q.prob x|)≤∑ x∈E,(p.prob x+q.prob x) := by
    apply Finset.sum_le_sum
    intro x _
    have hh := abs_sub_le (p.prob x) 0 (q.prob x)
    simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg (p.nonneg x),abs_of_nonneg (q.nonneg x)] using hh
  rw [Finset.sum_add_distrib,hmass] at hs
  rw [←hsplit]
  linarith


/-- Assemble the joint-law hybrid once the operational no-hit equality and
actual conditional oracle hybrid are proved. Neither semantic obligation is
hidden in a record field or certified by this probability calculation. -/
theorem joint_first_hit_bound {H T : Type} [Fintype H] [DecidableEq H]
    [Fintype T] [DecidableEq T] (μ : FinDist H) (actual dummy baseline : H → FinDist T)
    (E : Finset (H × T)) (δ v : ℝ)
    (hd : (∑ h,μ.prob h*((∑ t,|(dummy h).prob t-(baseline h).prob t|)/2))≤δ)
    (hv : (∑ ht∈E,(jointLaw μ baseline).prob ht)≤v)
    (hn : ∀ ht∉E,(jointLaw μ actual).prob ht=(jointLaw μ dummy).prob ht) :
    (∑ ht,|(jointLaw μ actual).prob ht-(jointLaw μ baseline).prob ht|)/2≤2*δ+v := by
  have hhit := hidden_event_transfer μ dummy baseline E δ hd
  have ha := first_hit_variation (jointLaw μ actual) (jointLaw μ dummy) E hn
  have ht : (∑ ht,|(jointLaw μ actual).prob ht-(jointLaw μ baseline).prob ht|)≤
      (∑ ht,|(jointLaw μ actual).prob ht-(jointLaw μ dummy).prob ht|)+
      (∑ ht,|(jointLaw μ dummy).prob ht-(jointLaw μ baseline).prob ht|) := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun ht _ => abs_sub_le _ _ _)
  have hj := joint_variation_identity μ dummy baseline
  linarith

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
