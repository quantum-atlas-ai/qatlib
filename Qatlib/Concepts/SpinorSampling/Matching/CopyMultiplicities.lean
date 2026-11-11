/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
import Qatlib.Concepts.SpinorSampling.Matching.UniformMatchedSampling
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

/-!
# Copy Multiplicities

The actual uniform address law of Q independent supplied copies.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Matching.Matched
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- The actual uniform address law of Q independent supplied copies. -/
def uniformCopyLaw (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (Q : ℕ) :
    FinDist (Fin Q → A) := independentSampleLaw (fun _ => uniformLaw A)

/-- Every full address sequence has its original exact product mass. -/
theorem uniformCopyLaw_prob (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    (Q : ℕ) (x : Fin Q → A) :
    (uniformCopyLaw A Q).prob x=1/(Fintype.card A : ℝ)^Q := by
  simp only [uniformCopyLaw,independentSampleLaw,uniformLaw,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,one_div_pow]

/-- A literal coordinate indicator records one occurrence of an address. -/
def addressIndicator {A : Type} [DecidableEq A] (a x : A) : ℝ := if x=a then 1 else 0

/-- A uniform actual coordinate has its exact point probability. -/
theorem uniform_indicator_expect {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (a : A) :
    (uniformLaw A).expect (addressIndicator a)=1/(Fintype.card A : ℝ) := by
  simp [FinDist.expect,addressIndicator,uniformLaw]

/-- A product with two distinct exceptional coordinates evaluates exactly at those two coordinates. -/
theorem two_coordinate_product {Q : ℕ} (i j : Fin Q) (hij : i≠j) (f g : Fin Q → ℝ) :
    (∏ k,if k=i then f k else if k=j then g k else 1)=f i*g j := by
  have hp (k : Fin Q) : (if k=i then f k else if k=j then g k else 1)=
      (if k=i then f k else 1)*(if k=j then g k else 1) := by
    by_cases hki : k=i <;> by_cases hkj : k=j <;> simp_all
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp only [Fintype.prod_ite_eq']

/-- Distinct actual supplied-copy coordinates have the exact product indicator expectation. -/
theorem uniform_two_indicator_expect {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    {Q : ℕ} (i j : Fin Q) (hij : i≠j) (a b : A) :
    (uniformCopyLaw A Q).expect (fun x => addressIndicator a (x i)*addressIndicator b (x j))=
      1/(Fintype.card A : ℝ)^2 := by
  let f : Fin Q → A → ℝ := fun k z => if k=i then addressIndicator a z else
    if k=j then addressIndicator b z else 1
  have hfun : (fun x : Fin Q → A => addressIndicator a (x i)*addressIndicator b (x j))=
      fun x => ∏ k,f k (x k) := by
    funext x
    exact (two_coordinate_product i j hij (fun k => addressIndicator a (x k))
      (fun k => addressIndicator b (x k))).symm
  rw [hfun]
  change (independentSampleLaw (fun _ : Fin Q => uniformLaw A)).expect _= _
  rw [independentSampleLaw_expect_prod]
  have hm (k : Fin Q) : (∑ z,(uniformLaw A).prob z*f k z)=
      if k=i then 1/(Fintype.card A : ℝ) else
        if k=j then 1/(Fintype.card A : ℝ) else 1 := by
    by_cases hki : k=i
    · simpa only [FinDist.expect,f,ite_eq_left hki] using uniform_indicator_expect a
    · by_cases hkj : k=j
      · simpa only [FinDist.expect,f,ite_eq_right hki,ite_eq_left hkj] using uniform_indicator_expect b
      · simpa only [f,ite_eq_right hki,ite_eq_right hkj,mul_one] using (uniformLaw A).sum_one
  simp_rw [hm]
  rw [two_coordinate_product i j hij]
  ring

/-- The true multiplicity is exactly the sum of the actual coordinate indicators. -/
theorem multiplicity_eq_indicator {A : Type} [Fintype A] [DecidableEq A]
    {Q : ℕ} (x : Fin Q → A) (a : A) :
    (multiplicity x a : ℝ)=∑ j,addressIndicator a (x j) := by
  have hn : Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity x a=
      ∑ j : Fin Q,if x j=a then (1 : ℕ) else 0 := by
    rw [Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity,
      Fintype.card_subtype,←Finset.sum_filter]
    simp
  unfold addressIndicator
  exact_mod_cast hn

/-- Actual address multiplicities exhaust the supplied copy positions. -/
theorem multiplicity_total {A : Type} [Fintype A] [DecidableEq A]
    {Q : ℕ} (x : Fin Q → A) : (∑ a,multiplicity x a)=Q := by
  simpa only [Nat.cast_id,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity,Fintype.card_fin] using (Fintype.sum_fiberwise' x (fun _ => (1 : ℕ)))

/-- Two distinct addresses have the actual multinomial cross moment under the same supplied-copy law. -/
theorem actual_count_cross_moment {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (Q : ℕ) (a b : A) (hab : a≠b) :
    (uniformCopyLaw A Q).expect (fun x => (multiplicity x a : ℝ)*(multiplicity x b : ℝ))=
      (Q : ℝ)*((Q : ℝ)-1)/(Fintype.card A : ℝ)^2 := by
  have hproduct (x : Fin Q → A) :
      (multiplicity x a : ℝ)*(multiplicity x b : ℝ)=
        ∑ i : Fin Q,∑ j : Fin Q,addressIndicator a (x i)*addressIndicator b (x j) := by
    rw [multiplicity_eq_indicator,multiplicity_eq_indicator,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have he (i j : Fin Q) :
      (uniformCopyLaw A Q).expect (fun x => addressIndicator a (x i)*addressIndicator b (x j))=
        if i=j then 0 else 1/(Fintype.card A : ℝ)^2 := by
    by_cases hij : i=j
    · subst j
      have hz (x : Fin Q → A) : addressIndicator a (x i)*addressIndicator b (x i)=0 := by
        unfold addressIndicator
        split_ifs <;> simp_all
      simp only [hz,FinDist.expect,mul_zero,Finset.sum_const_zero,ite_true]
    · rw [ite_eq_right hij]
      exact uniform_two_indicator_expect i j hij a b
  have hi (i : Fin Q) :
      (∑ j : Fin Q,if i=j then (0 : ℝ) else 1/(Fintype.card A : ℝ)^2)=
        (Q : ℝ)/(Fintype.card A : ℝ)^2-1/(Fintype.card A : ℝ)^2 := by
    have ht (j : Fin Q) : (if i=j then (0 : ℝ) else 1/(Fintype.card A : ℝ)^2)=
        1/(Fintype.card A : ℝ)^2-(if i=j then 1/(Fintype.card A : ℝ)^2 else 0) := by
      split_ifs <;> ring
    simp_rw [ht]
    rw [Finset.sum_sub_distrib]
    simp [div_eq_mul_inv]
  have hfun : (fun x : Fin Q → A => (multiplicity x a : ℝ)*(multiplicity x b : ℝ))=
      fun x => ∑ i : Fin Q,∑ j : Fin Q,addressIndicator a (x i)*addressIndicator b (x j) :=
    funext hproduct
  rw [hfun]
  have hlin : (uniformCopyLaw A Q).expect (fun x =>
      ∑ i : Fin Q,∑ j : Fin Q,addressIndicator a (x i)*addressIndicator b (x j))=
        ∑ i : Fin Q,∑ j : Fin Q,(uniformCopyLaw A Q).expect
          (fun x => addressIndicator a (x i)*addressIndicator b (x j)) := by
    simp only [FinDist.expect,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hlin]
  simp_rw [he,hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The integer paired minimum is bounded by the actual count product, including zero counts. -/
theorem min_count_le_product (a b : ℕ) : min a b ≤ a*b := by
  by_cases hb : b=0
  · simp [hb]
  · calc min a b ≤ a := Nat.min_le_left _ _
         _ = a*1 := by simp
         _ ≤ a*b := Nat.mul_le_mul_left a (by omega)

/-- The actual total paired collision count in the full address sequence. -/
def pairedMinCount {E : Type} [Fintype E] [DecidableEq E] {Q : ℕ}
    (x : Fin Q → E × Bool) : ℕ := ∑ e,min (multiplicity x (e,false)) (multiplicity x (e,true))

/-- Pairwise minimum counts cannot use more than half the actual supplied copy positions. -/
theorem pairedMinCount_twice_le {E : Type} [Fintype E] [DecidableEq E] {Q : ℕ}
    (x : Fin Q → E × Bool) : 2*pairedMinCount x ≤ Q := by
  calc 2*pairedMinCount x = ∑ e,2*min (multiplicity x (e,false)) (multiplicity x (e,true)) := by
         rw [pairedMinCount,Finset.mul_sum]
       _ ≤ ∑ e,(multiplicity x (e,false)+multiplicity x (e,true)) :=
         Finset.sum_le_sum fun e _ => by omega
       _ = ∑ a : E × Bool,multiplicity x a := by
         rw [Fintype.sum_prod_type]
         apply Finset.sum_congr rfl
         intro e _
         simp only [Fintype.sum_bool,add_comm]
       _ = Q := multiplicity_total x

/-- The same actual supplied-copy law gives the actual half-count bound. -/
theorem pairedMinCount_expect_half {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (Q : ℕ) : (uniformCopyLaw (E × Bool) Q).expect (fun x => (pairedMinCount x : ℝ)) ≤ (Q : ℝ)/2 := by
  let p := uniformCopyLaw (E × Bool) Q
  have hp (x : Fin Q → E × Bool) : (pairedMinCount x : ℝ) ≤ (Q : ℝ)/2 := by
    have h := pairedMinCount_twice_le x
    have hr : (2 : ℝ)*(pairedMinCount x : ℝ) ≤ (Q : ℝ) := by exact_mod_cast h
    linarith
  calc _ ≤ ∑ x,p.prob x*((Q : ℝ)/2) :=
         Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (p.nonneg x)
       _ = _ := by rw [←Finset.sum_mul,p.sum_one,one_mul]

/-- The true multinomial count moment gives the collision-sensitive expectation bound. -/
theorem pairedMinCount_expect_collision {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (Q : ℕ) : (uniformCopyLaw (E × Bool) Q).expect (fun x => (pairedMinCount x : ℝ)) ≤
      (Q : ℝ)*((Q : ℝ)-1)/(2*(Fintype.card (E × Bool) : ℝ)) := by
  let p := uniformCopyLaw (E × Bool) Q
  have hp (x : Fin Q → E × Bool) : (pairedMinCount x : ℝ) ≤
      ∑ e,(multiplicity x (e,false) : ℝ)*(multiplicity x (e,true) : ℝ) := by
    unfold pairedMinCount
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro e _
    exact_mod_cast min_count_le_product (multiplicity x (e,false)) (multiplicity x (e,true))
  calc _ ≤ p.expect (fun x => ∑ e,(multiplicity x (e,false) : ℝ)*(multiplicity x (e,true) : ℝ)) :=
         Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (p.nonneg x)
       _ = ∑ e : E,p.expect (fun x => (multiplicity x (e,false) : ℝ)*(multiplicity x (e,true) : ℝ)) := by
         simp only [FinDist.expect,Finset.mul_sum]
         rw [Finset.sum_comm]
       _ = ∑ _e : E,(Q : ℝ)*((Q : ℝ)-1)/(Fintype.card (E × Bool) : ℝ)^2 := by
         apply Finset.sum_congr rfl
         intro e _
         exact actual_count_cross_moment Q (e,false) (e,true) (by simp)
       _ = _ := by
         have hE : (Fintype.card E : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
         simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
         field_simp [hE]

/-- Both sharp occupancy scales are derived from the actual address product law, with Q=0 and Q=1 retained. -/
theorem actual_paired_count_expect {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (Q : ℕ) : (uniformCopyLaw (E × Bool) Q).expect (fun x => (pairedMinCount x : ℝ)) ≤
      min ((Q : ℝ)/2) ((Q : ℝ)*((Q : ℝ)-1)/(2*(Fintype.card (E × Bool) : ℝ))) :=
  le_min (pairedMinCount_expect_half Q) (pairedMinCount_expect_collision Q)

end Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
