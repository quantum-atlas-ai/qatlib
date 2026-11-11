/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.Concentration.SubsetProducts.FiniteMaclaurin

/-!
# Finite Maclaurin Bound

Finite Maclaurin Bound constructions and identities for Probability Core.
-/

set_option autoImplicit false

namespace Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin
noncomputable section
open scoped BigOperators Classical

variable {S : Type*} [DecidableEq S]

omit [DecidableEq S] in
/-- Complete original `covariance_double_sum` guarantee for `FiniteMaclaurinBound`; all source hypotheses and output obligations are retained. -/
theorem covariance_double_sum (R : Finset S) (a w : S → ℝ) :
    (∑ i ∈ R,∑ j ∈ R,(a i-a j)*(w j-w i))=
      2*((∑ i ∈ R,a i)*(∑ i ∈ R,w i)-(R.card : ℝ)*(∑ i ∈ R,a i*w i)) := by
  have hp (i j : S) : (a i-a j)*(w j-w i)=
      a i*w j-a i*w i-a j*w j+a j*w i := by ring
  have h1 : (∑ i ∈ R,∑ j ∈ R,a i*w j)=(∑ i ∈ R,a i)*(∑ i ∈ R,w i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.mul_sum _ _ _).symm
  have h2 : (∑ i ∈ R,∑ _j ∈ R,a i*w i)=(R.card : ℝ)*(∑ i ∈ R,a i*w i) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [Finset.mul_sum]
  have h3 : (∑ _i ∈ R,∑ j ∈ R,a j*w j)=(R.card : ℝ)*(∑ i ∈ R,a i*w i) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
  have h4 : (∑ i ∈ R,∑ j ∈ R,a j*w i)=(∑ i ∈ R,a i)*(∑ i ∈ R,w i) := by
    simp_rw [← Finset.sum_mul]
    exact (Finset.mul_sum _ _ _).symm
  simp_rw [hp,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [h1,h2,h3,h4]
  ring

-- Nonnegative square weights supply the full, all-positive-vector recursion.
/-- Complete original `elementary_ratio_step` guarantee for `FiniteMaclaurinBound`; all source hypotheses and output obligations are retained. -/
theorem elementary_ratio_step (R : Finset S) (a : S → ℝ)
    (ha : ∀ x∈R,0≤a x) (k : ℕ) :
    (R.card : ℝ)*((k+2 : ℕ) : ℝ)*elementary R a (k+2)≤
      ((R.card : ℝ)-((k+1 : ℕ) : ℝ))*(∑ x ∈ R,a x)*elementary R a (k+1) := by
  let w := fun i => elementary (R.erase i) a (k+1)
  have hn : 0≤∑ i ∈ R,∑ j ∈ R,(a i-a j)*(w j-w i) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    by_cases hij : i=j
    · subst j
      simp
    · have hd := deletion_difference R a j i hj hi (fun h => hij h.symm) k
      have he : 0≤elementary ((R.erase j).erase i) a k :=
        elementary_nonneg _ a (fun x hx => ha x
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))) k
      change 0≤(a i-a j)*(elementary (R.erase j) a (k+1)-elementary (R.erase i) a (k+1))
      rw [hd]
      nlinarith [sq_nonneg (a i-a j),mul_nonneg (sq_nonneg (a i-a j)) he]
  rw [covariance_double_sum] at hn
  dsimp [w] at hn
  rw [deletion_sum R a (k+1),weighted_deletion_sum R a (k+1)] at hn
  have hcast : ((k+1+1 : ℕ) : ℝ)=((k+2 : ℕ) : ℝ) := by congr 1
  rw [hcast] at hn
  nlinarith


-- The unscaled form also covers k beyond the population size without
-- conditioning on a positive event or dividing by a zero binomial count.
/-- Complete original `elementary_le_mean_pow` guarantee for `FiniteMaclaurinBound`; all source hypotheses and output obligations are retained. -/
theorem elementary_le_mean_pow (R : Finset S) (a : S → ℝ)
    (ha : ∀ x∈R,0≤a x) (k : ℕ) :
    elementary R a k≤(R.card.choose k : ℝ)*((∑ x ∈ R,a x)/(R.card : ℝ))^k := by
  by_cases hR : R.card=0
  · have he : R=∅ := Finset.card_eq_zero.mp hR
    subst R
    cases k <;> simp
  have hM : (0 : ℝ)<R.card := by exact_mod_cast (Nat.pos_of_ne_zero hR)
  let T : ℝ := ∑ x ∈ R,a x
  let μ : ℝ := T/(R.card : ℝ)
  have hT0 : 0≤T := Finset.sum_nonneg ha
  have hT : T=(R.card : ℝ)*μ := by
    exact (mul_div_cancel₀ _ hM.ne').symm
  change elementary R a k≤(R.card.choose k : ℝ)*μ^k
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k+1≤R.card
    · cases k with
      | zero =>
        simp only [Nat.zero_add,elementary_one,Nat.choose_one_right,pow_one]
        exact hT.le
      | succ r =>
        have hrpos : (0 : ℝ)<((r+2 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ (r+1)
        have hd := mul_pos hM hrpos
        apply le_of_mul_le_mul_left _ hd
        have hr : r+1≤R.card := Nat.le_trans (Nat.le_succ _) hk
        have hrR : ((r+1 : ℕ) : ℝ)≤R.card := by exact_mod_cast hr
        have hc : (R.card.choose (r+2) : ℝ)*((r+2 : ℕ) : ℝ)=
            (R.card.choose (r+1) : ℝ)*((R.card : ℝ)-((r+1 : ℕ) : ℝ)) := by
          rw [← Nat.cast_sub hr]
          exact_mod_cast Nat.choose_succ_right_eq R.card (r+1)
        calc
          _ ≤ ((R.card : ℝ)-((r+1 : ℕ) : ℝ))*T*elementary R a (r+1) :=
            elementary_ratio_step R a ha r
          _ ≤ ((R.card : ℝ)-((r+1 : ℕ) : ℝ))*T*
              ((R.card.choose (r+1) : ℝ)*μ^(r+1)) :=
            mul_le_mul_of_nonneg_left ih (mul_nonneg (sub_nonneg.mpr hrR) hT0)
          _ = _ := by
            rw [hT,pow_succ μ (r+1)]
            have hm := congrArg (fun z : ℝ => (R.card : ℝ)*z*(μ^(r+1)*μ)) hc
            convert hm.symm using 1 <;> ring
    · have hl : R.card<k+1 := Nat.lt_of_not_ge hk
      rw [elementary,Finset.powersetCard_eq_empty.mpr hl,Finset.sum_empty,
        Nat.choose_eq_zero_of_lt hl,Nat.cast_zero,zero_mul]

omit [DecidableEq S] in
/-- Complete original `subset_product_mean_bound` guarantee for `FiniteMaclaurinBound`; all source hypotheses and output obligations are retained. -/
theorem subset_product_mean_bound [Fintype S]
    (a : S → ℝ) (ha : ∀ x,0≤a x) (k : ℕ) :
    (1/(Fintype.card S).choose k : ℝ)*
      (∑ A ∈ (Finset.univ : Finset S).powersetCard k,∏ x ∈ A,a x)≤
        ((∑ x : S,a x)/(Fintype.card S : ℝ))^k := by
  classical
  by_cases hk : k≤Fintype.card S
  · have hc : (0 : ℝ)<(Fintype.card S).choose k := by exact_mod_cast Nat.choose_pos hk
    have h := elementary_le_mean_pow (Finset.univ : Finset S) a (fun x _ => ha x) k
    simp only [elementary,Finset.card_univ] at h
    have hd : ((∑ A ∈ (Finset.univ : Finset S).powersetCard k,∏ x ∈ A,a x)/
        ((Fintype.card S).choose k : ℝ))≤((∑ x : S,a x)/(Fintype.card S : ℝ))^k :=
      (div_le_iff₀ hc).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hd
  · have hl : (Finset.univ : Finset S).card<k := by simpa using Nat.lt_of_not_ge hk
    rw [Finset.powersetCard_eq_empty.mpr hl,Finset.sum_empty,mul_zero]
    exact pow_nonneg (div_nonneg (Finset.sum_nonneg (fun x _ => ha x)) (Nat.cast_nonneg _)) k

end
end Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin

#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.covariance_double_sum
#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.elementary_ratio_step

#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.elementary_le_mean_pow
#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.subset_product_mean_bound
