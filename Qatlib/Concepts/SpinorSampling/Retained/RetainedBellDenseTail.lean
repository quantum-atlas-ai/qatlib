/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellAddressLaw

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Dense Tail

Retained Bell Dense Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Construction for grouped Match Total in the retained bell dense tail model. -/
def groupedMatchTotal {n m K : ℕ} (τ : S → S)
    (z : Fin K → (Fin n → S) × (Fin m → S)) : ℝ :=
  ∑ j : Fin K,matchedAddressCount τ (z j).1 (z j).2

/-- Construction for flat Match Total in the retained bell dense tail model. -/
def flatMatchTotal (τ : S → S) (n m K : ℕ)
    (A : Fin (Fintype.card (AddressIndex n m K)) → S) : ℝ :=
  groupedMatchTotal τ (addressBlocksEquiv n m K A)

/-- Complete original `pooled_small_as_flat` guarantee for `RetainedBellDenseTail`; all source hypotheses and output obligations are retained. -/
theorem pooled_small_as_flat (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (n m K : ℕ) (r₀ : ℝ) :
    pooledSmallMass (n:=n) (m:=m) (K:=K) a b c k hz τ r₀=
      (cohortLaw (uniformLaw S) (Fintype.card (AddressIndex n m K))).expect
        (fun A => if flatMatchTotal τ n m K A<r₀ then 1 else 0) := by
  have he := observation_blocks_flat_address_expect a b c k hz τ n m K
    (fun z => if groupedMatchTotal τ z<r₀ then (1 : ℝ) else 0)
  have hcount (ω : Fin K → CohortObservation n m τ) :
      groupedMatchTotal τ (fun j => ((ω j).1,(ω j).2.1))=(pooledMatches τ ω : ℝ) := by
    simp only [groupedMatchTotal,matchedAddressCount,pooledMatches,observedRvec,Nat.cast_sum]
  simpa only [hcount,pooledSmallMass,flatMatchTotal] using he

/-- Complete original `flat_dense_mean_lower` guarantee for `RetainedBellDenseTail`; all source hypotheses and output obligations are retained. -/
theorem flat_dense_mean_lower (τ : S → S) (K : ℕ) :
    (K : ℝ)*(Fintype.card S : ℝ)/4≤
      (cohortLaw (uniformLaw S)
        (Fintype.card (AddressIndex (Fintype.card S) (Fintype.card S) K))).expect
          (flatMatchTotal τ (Fintype.card S) (Fintype.card S) K) := by
  let M := Fintype.card S
  let p := productLaw (cohortLaw (uniformLaw S) M) (cohortLaw (uniformLaw S) M)
  have he := grouped_address_expect_flat (S:=S) M M K (groupedMatchTotal τ)
  change _≤(cohortLaw (uniformLaw S) (Fintype.card (AddressIndex M M K))).expect
    (fun A => groupedMatchTotal τ (addressBlocksEquiv M M K A))
  rw [← he]
  have hcoord (j : Fin K) :
      (cohortLaw p K).expect (fun z => matchedAddressCount τ (z j).1 (z j).2)=
        p.expect (fun z => matchedAddressCount τ z.1 z.2) :=
    p.expect_coord j (fun z => matchedAddressCount τ z.1 z.2)
  change _≤(cohortLaw p K).expect (fun z => ∑ j,matchedAddressCount τ (z j).1 (z j).2)
  rw [finite_expect_sum]
  simp_rw [hcoord]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_left (matched_dense_mean_lower (S:=S) τ)
    (Nat.cast_nonneg (α:=ℝ) K)
  convert hh using 1
  ring

-- A single captured address changes one block's cardinality by at most one.
omit [Fintype S] [Nonempty S] in
/-- Complete original `flat_match_coordinate` guarantee for `RetainedBellDenseTail`; all source hypotheses and output obligations are retained. -/
theorem flat_match_coordinate (τ : Equiv.Perm S) (n m K : ℕ)
    (A B : Fin (Fintype.card (AddressIndex n m K)) → S)
    (i : Fin (Fintype.card (AddressIndex n m K)))
    (h : ∀ t,t≠i → A t=B t) :
    |flatMatchTotal τ n m K A-flatMatchTotal τ n m K B|≤1 := by
  let u := (addressCode n m K).symm i
  let ZA := addressBlocksEquiv n m K A
  let ZB := addressBlocksEquiv n m K B
  have hcode (j : Fin K) (v : Fin n ⊕ Fin m) (he : addressCode n m K (j,v)=i) :
      (j,v)=u := by
    simpa only [Equiv.symm_apply_apply] using congrArg (addressCode n m K).symm he
  have hrest (j : Fin K) (hj : j≠u.1) : ZA j=ZB j := by
    apply Prod.ext <;> funext v
    · change A (addressCode n m K (j,Sum.inl v))=B (addressCode n m K (j,Sum.inl v))
      exact h _ (fun he => hj (congrArg Prod.fst (hcode j (Sum.inl v) he)))
    · change A (addressCode n m K (j,Sum.inr v))=B (addressCode n m K (j,Sum.inr v))
      exact h _ (fun he => hj (congrArg Prod.fst (hcode j (Sum.inr v) he)))
  have hsum : flatMatchTotal τ n m K A-flatMatchTotal τ n m K B=
      matchedAddressCount τ (ZA u.1).1 (ZA u.1).2-
        matchedAddressCount τ (ZB u.1).1 (ZB u.1).2 := by
    change (∑ j,matchedAddressCount τ (ZA j).1 (ZA j).2)-
      (∑ j,matchedAddressCount τ (ZB j).1 (ZB j).2)=_
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single u.1
    · intro j _ hj
      rw [hrest j hj,sub_self]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  rw [hsum]
  cases hu : u.2 with
  | inl v =>
    have hright : (ZA u.1).2=(ZB u.1).2 := by
      funext w
      apply h
      intro he
      have hc := congrArg Prod.snd (hcode u.1 (Sum.inr w) he)
      rw [hu] at hc
      cases hc
    rw [hright]
    apply matched_count_left_coordinate τ (ZA u.1).1 (ZB u.1).1 (ZB u.1).2 v
    intro w hw
    apply h
    intro he
    have hc := congrArg Prod.snd (hcode u.1 (Sum.inl w) he)
    rw [hu] at hc
    exact hw (Sum.inl.inj hc)
  | inr v =>
    have hleft : (ZA u.1).1=(ZB u.1).1 := by
      funext w
      apply h
      intro he
      have hc := congrArg Prod.snd (hcode u.1 (Sum.inl w) he)
      rw [hu] at hc
      cases hc
    rw [hleft]
    apply matched_count_right_coordinate τ (ZB u.1).1 (ZA u.1).2 (ZB u.1).2 v
    intro w hw
    apply h
    intro he
    have hc := congrArg Prod.snd (hcode u.1 (Sum.inr w) he)
    rw [hu] at hc
    exact hw (Sum.inr.inj hc)

/-- Complete original `dense_small_match_tail` guarantee for `RetainedBellDenseTail`; all source hypotheses and output obligations are retained. -/
theorem dense_small_match_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (K : ℕ) :
    pooledSmallMass (n:=Fintype.card S) (m:=Fintype.card S) (K:=K) a b c k hz τ
      ((K : ℝ)*(Fintype.card S : ℝ)/8)≤
        Real.exp (-(K : ℝ)*(Fintype.card S : ℝ)/64) := by
  by_cases hK : K=0
  · subst K
    simp only [Nat.cast_zero,zero_mul,zero_div,neg_zero,Real.exp_zero]
    unfold pooledSmallMass
    simp only [pooledMatches,Fin.sum_univ_zero,Nat.cast_zero,lt_self_iff_false,ite_false]
    rw [finite_expect_const]
    norm_num
  · let M := Fintype.card S
    let N := Fintype.card (AddressIndex M M K)
    let F := flatMatchTotal τ M M K
    let p := cohortLaw (uniformLaw S) N
    have hM : (0 : ℝ)<M := by dsimp [M]; exact_mod_cast Fintype.card_pos
    have hKR : (0 : ℝ)<K := by exact_mod_cast Nat.pos_of_ne_zero hK
    have hN : (N : ℝ)=2*(K : ℝ)*(M : ℝ) := by
      dsimp [N]
      simp only [AddressIndex,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,
        Nat.cast_mul,Nat.cast_add]
      ring
    have hsum : (∑ _i : Fin N,(1 : ℝ)^2)=2*(K : ℝ)*(M : ℝ) := by
      simpa only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one] using hN
    have hmean :
        (independentSampleLaw (fun _i : Fin N => uniformLaw S)).expect (fun A => -F A)=
          -p.expect F := by
      simp only [FinDist.expect,independentSampleLaw,p,cohortLaw,FinDist.probOf,
        mul_neg,← Finset.sum_neg_distrib]
    have ht := (finite_product_bounded_differences_tail S N
      (fun _ => uniformLaw S) (fun A => -F A) (fun _ => 1) ((K : ℝ)*(M : ℝ)/8)
      (fun _ => by norm_num) (by rw [hsum]; positivity) (by positivity)
      (by
        intro i A B hAB
        simpa only [neg_sub_neg,abs_sub_comm] using flat_match_coordinate τ M M K A B i hAB)).1
    rw [hmean,hsum] at ht
    have he : -2*((K : ℝ)*(M : ℝ)/8)^2/(2*(K : ℝ)*(M : ℝ))=
        -(K : ℝ)*(M : ℝ)/64 := by
      field_simp [hKR.ne',hM.ne']
      ring
    rw [he] at ht
    have hμ := flat_dense_mean_lower (S:=S) τ K
    rw [pooled_small_as_flat]
    change p.expect (fun A => if F A<(K : ℝ)*(M : ℝ)/8 then 1 else 0)≤_
    calc
      _ ≤ p.expect (fun A => if -p.expect F+(K : ℝ)*(M : ℝ)/8≤-F A then 1 else 0) := by
        apply finite_expect_mono
        intro A
        by_cases hA : F A<(K : ℝ)*(M : ℝ)/8
        · have hh : -p.expect F+(K : ℝ)*(M : ℝ)/8≤-F A := by
            change (K : ℝ)*(M : ℝ)/4≤p.expect F at hμ
            linarith
          simp only [ite_eq_left hA,ite_eq_left hh,le_refl]
        · simp only [ite_eq_right hA]
          split_ifs <;> norm_num
      _ = ∑ A ∈ Finset.univ.filter (fun A : Fin N → S =>
          -p.expect F+(K : ℝ)*(M : ℝ)/8≤-F A),
          (independentSampleLaw (fun _i : Fin N => uniformLaw S)).prob A := by
        rw [Finset.sum_filter]
        unfold FinDist.expect
        simp only [p,cohortLaw,independentSampleLaw,FinDist.probOf,mul_ite,mul_one,mul_zero]
      _ ≤ _ := ht

/-- Complete original `clipped_pooled_dense_tail` guarantee for `RetainedBellDenseTail`; all source hypotheses and output obligations are retained. -/
theorem clipped_pooled_dense_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (K : ℕ)
    (p₀ : ℚ) (ε : ℝ) (hmean : bellMean a b c k τ≤(p₀ : ℝ)) (hε : 0<ε) :
    (freshObservationBlocks (n:=Fintype.card S) (m:=Fintype.card S) a b c k hz τ K).expect
      (fun ω => if ε< |(clippedPooledMeanQ p₀ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)≤
        Real.exp (-(K : ℝ)*(Fintype.card S : ℝ)/64)+
          2*Real.exp (-((K : ℝ)*(Fintype.card S : ℝ)/8)*ε^2/(4*((p₀ : ℝ)+ε))) := by
  exact (clipped_pooled_unconditional_tail a b c k hz τ p₀ ε
    ((K : ℝ)*(Fintype.card S : ℝ)/8) hmean hε).trans
      (add_le_add (dense_small_match_tail a b c k hz τ K) (le_refl _))

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_small_as_flat
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.flat_dense_mean_lower
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.flat_match_coordinate
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.dense_small_match_tail
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.clipped_pooled_dense_tail
