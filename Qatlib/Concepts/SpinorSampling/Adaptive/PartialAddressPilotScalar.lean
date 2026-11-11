/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPlan

set_option backward.isDefEq.respectTransparency false

/-!
Finite iid target-box/sign records: none means this copy missed the target
box, and some b records its observed sign. The empirical mean is zero in an
empty box. The risk bound is derived from the full record law, weighted
centered moments and exchangeability; no count or success certificate is an
input. Transport from the original native Pauli/address measurements to this
collapsed law, balanced-box geometry and three-coordinate aggregation remain
separate obligations. This module alone is not the complete pilot algorithm.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotScalar
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Construction for weight in the partial address pilot scalar model. -/
def weight (p μ : ℝ) : Option Bool → ℝ
  | none => 1-p
  | some b => p*(1+bitSign b*μ)/2

/-- Construction for law in the partial address pilot scalar model. -/
def law (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1) : FinDist (Option Bool) where
  prob := weight p μ
  nonneg r := by
    rcases r with _ | b
    · exact sub_nonneg.mpr hp.2
    · cases b <;> dsimp [weight,bitSign]
      · exact div_nonneg (mul_nonneg hp.1 (by linarith [abs_le.mp hμ])) (by norm_num)
      · exact div_nonneg (mul_nonneg hp.1 (by linarith [abs_le.mp hμ])) (by norm_num)
  sum_one := by
    norm_num [Fintype.sum_option,Fintype.sum_bool,weight,bitSign]
    ring

/-- Construction for hit in the partial address pilot scalar model. -/
def hit : Option Bool → ℕ
  | none => 0
  | some _ => 1

/-- Construction for sign in the partial address pilot scalar model. -/
def sign : Option Bool → ℝ
  | none => 0
  | some b => bitSign b

/-- Construction for count in the partial address pilot scalar model. -/
def count {n : ℕ} (ω : Fin n → Option Bool) : ℕ := ∑ i,hit (ω i)
/-- Construction for centered in the partial address pilot scalar model. -/
def centered {n : ℕ} (μ : ℝ) (ω : Fin n → Option Bool) : ℝ :=
  ∑ i,(sign (ω i)-μ*(hit (ω i) : ℝ))

/-- Complete original `count_cons` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem count_cons {n : ℕ} (r : Option Bool) (ω : Fin n → Option Bool) :
    count (Fin.cons r ω)=hit r+count ω := by simp [count,Fin.sum_univ_succ]

/-- Complete original `centered_cons` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem centered_cons {n : ℕ} (μ : ℝ) (r : Option Bool) (ω : Fin n → Option Bool) :
    centered μ (Fin.cons r ω)=sign r-μ*(hit r : ℝ)+centered μ ω := by
  simp [centered,Fin.sum_univ_succ]
  ring

/-- Construction for total in the partial address pilot scalar model. -/
def total (d : FinDist (Option Bool)) {n : ℕ} (f : (Fin n → Option Bool) → ℝ) : ℝ :=
  ∑ ω,d.probOf ω*f ω

/-- Complete original `total_cons` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_cons (d : FinDist (Option Bool)) {n : ℕ}
    (f : (Fin (n+1) → Option Bool) → ℝ) :
    total d f=∑ r : Option Bool,d.prob r*total d (fun ω : Fin n → Option Bool => f (Fin.cons r ω)) :=
  product_expect_cons d f

/-- Complete original `conditional_square` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem conditional_square (p μ z : ℝ) (c : ℕ) (f : ℕ → ℝ) :
    (∑ r : Option Bool,weight p μ r*((sign r-μ*(hit r : ℝ)+z)^2*f (hit r+c)))=
      (1-p)*z^2*f c+p*(z^2+1-μ^2)*f (c+1) := by
  norm_num [Fintype.sum_option,Fintype.sum_bool,weight,sign,hit,bitSign,Nat.add_comm 1 c]
  ring

/-- Complete original `total_cons_swapped` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_cons_swapped (d : FinDist (Option Bool)) {n : ℕ}
    (f : (Fin (n+1) → Option Bool) → ℝ) :
    total d f=∑ ω : Fin n → Option Bool,d.probOf ω*(∑ r : Option Bool,d.prob r*f (Fin.cons r ω)) := by
  rw [total_cons]
  unfold total
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Complete original `law_prob` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem law_prob (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1) (r : Option Bool) :
    (law p μ hp hμ).prob r=weight p μ r := rfl

/-- Complete original `conditional_count` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem conditional_count (p μ : ℝ) (c : ℕ) (f : ℕ → ℝ) :
    (∑ r : Option Bool,weight p μ r*(((hit r+c : ℕ) : ℝ)*f (hit r+c)))=
      (1-p)*(c : ℝ)*f c+p*((c : ℝ)+1)*f (c+1) := by
  norm_num [Fintype.sum_option,Fintype.sum_bool,weight,hit,bitSign,Nat.add_comm 1 c]
  ring

/-- Complete original `weighted_square` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem weighted_square (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1) (n : ℕ) :
    ∀ f : ℕ → ℝ,
      total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (centered μ ω)^2*f (count ω))=
      (1-μ^2)*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (count ω : ℝ)*f (count ω)) := by
  induction n with
  | zero => intro f; simp [total,centered,count]
  | succ n ih =>
    intro f
    rw [total_cons_swapped,total_cons_swapped]
    simp_rw [law_prob,count_cons,centered_cons,conditional_square,conditional_count]
    have hleft :
        (∑ ω : Fin n → Option Bool,(law p μ hp hμ).probOf ω*
          ((1-p)*(centered μ ω)^2*f (count ω)+
            p*((centered μ ω)^2+1-μ^2)*f (count ω+1)))=
        (1-p)*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (centered μ ω)^2*f (count ω))+
        p*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (centered μ ω)^2*f (count ω+1))+
        p*(1-μ^2)*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => f (count ω+1)) := by
      simp only [total,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    have hright :
        (∑ ω : Fin n → Option Bool,(law p μ hp hμ).probOf ω*
          ((1-p)*(count ω : ℝ)*f (count ω)+p*((count ω : ℝ)+1)*f (count ω+1)))=
        (1-p)*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (count ω : ℝ)*f (count ω))+
        p*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (count ω : ℝ)*f (count ω+1))+
        p*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => f (count ω+1)) := by
      simp only [total,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    rw [hleft,hright,ih f,ih (fun c => f (c+1))]
    ring

/-- Complete original `total_add` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_add (d : FinDist (Option Bool)) {n : ℕ}
    (f g : (Fin n → Option Bool) → ℝ) :
    total d (fun ω => f ω+g ω)=total d f+total d g := by
  simp only [total,mul_add,Finset.sum_add_distrib]

/-- Complete original `total_mul` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_mul (d : FinDist (Option Bool)) {n : ℕ}
    (a : ℝ) (f : (Fin n → Option Bool) → ℝ) :
    total d (fun ω => a*f ω)=a*total d f := by
  unfold total
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Complete original `total_mono` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_mono (d : FinDist (Option Bool)) {n : ℕ}
    (f g : (Fin n → Option Bool) → ℝ) (hfg : ∀ ω,f ω ≤ g ω) :
    total d f ≤ total d g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (Finset.prod_nonneg fun i _ => d.nonneg (ω i))

/-- Construction for empirical in the partial address pilot scalar model. -/
def empirical {n : ℕ} (ω : Fin n → Option Bool) : ℝ :=
  (∑ i,sign (ω i))/(count ω : ℝ)

/-- Complete original `centered_sum` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem centered_sum {n : ℕ} (μ : ℝ) (ω : Fin n → Option Bool) :
    centered μ ω=(∑ i,sign (ω i))-μ*(count ω : ℝ) := by
  simp only [centered,count,Finset.sum_sub_distrib,Nat.cast_sum,Finset.mul_sum]

/-- Construction for risk Expression in the partial address pilot scalar model. -/
def riskExpression (μ : ℝ) (c : ℕ) : ℝ :=
  (1-μ^2)*((c : ℝ)*((c : ℝ)^2)⁻¹)+μ^2*(if c=0 then 1 else 0)

/-- Complete original `empirical_risk_identity` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem empirical_risk_identity {n : ℕ} (μ : ℝ) (ω : Fin n → Option Bool) :
    (empirical ω-μ)^2=(centered μ ω)^2*((count ω : ℝ)^2)⁻¹+
      μ^2*(if count ω=0 then 1 else 0) := by
  rw [centered_sum]
  by_cases h : count ω=0
  · simp [empirical,h]
  · have hc : (count ω : ℝ) ≠ 0 := by exact_mod_cast h
    simp only [empirical,ite_eq_right h,mul_zero,add_zero]
    field_simp

/-- Complete original `risk_expression_bound` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem risk_expression_bound (μ : ℝ) (hμ : |μ| ≤ 1) (c : ℕ) :
    riskExpression μ c ≤ 2/((c : ℝ)+1) := by
  have hμsq : μ^2 ≤ 1 := by nlinarith [abs_le.mp hμ |>.1,abs_le.mp hμ |>.2]
  by_cases h : c=0
  · subst c
    norm_num [riskExpression]
    linarith
  · have hc : (0 : ℝ)<c := by exact_mod_cast (Nat.pos_of_ne_zero h)
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    have he : riskExpression μ c=(1-μ^2)/(c : ℝ) := by
      simp only [riskExpression,ite_eq_right h,mul_zero,add_zero]
      field_simp
    rw [he]
    apply (div_le_div_iff₀ hc (by positivity : (0 : ℝ)<(c : ℝ)+1)).mpr
    nlinarith [sq_nonneg μ,mul_nonneg (sq_nonneg μ) (by positivity : (0 : ℝ) ≤ (c : ℝ)+1)]

/-- Complete original `empirical_risk_bound` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem empirical_risk_bound (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1) (n : ℕ) :
    total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (empirical ω-μ)^2) ≤
      2*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => 1/((count ω : ℝ)+1)) := by
  have he : total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (empirical ω-μ)^2)=
      total (law p μ hp hμ) (fun ω : Fin n → Option Bool => riskExpression μ (count ω)) := by
    simp_rw [empirical_risk_identity]
    rw [total_add,total_mul,weighted_square p μ hp hμ n (fun c => ((c : ℝ)^2)⁻¹)]
    simp only [riskExpression,total_add,total_mul]
  rw [he,← total_mul]
  exact total_mono _ _ _ (fun ω => by simpa only [mul_one_div] using risk_expression_bound μ hμ (count ω))

/-- Construction for reindex in the partial address pilot scalar model. -/
def reindex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → Option Bool) ≃ (Fin n → Option Bool) where
  toFun ω i := ω (e i)
  invFun ω i := ω (e.symm i)
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

/-- Complete original `count_reindex` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem count_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (ω : Fin n → Option Bool) :
    count (reindex e ω)=count ω := by
  exact Equiv.sum_comp e (fun i => hit (ω i))

/-- Complete original `prob_reindex` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem prob_reindex (d : FinDist (Option Bool)) {n : ℕ}
    (e : Equiv.Perm (Fin n)) (ω : Fin n → Option Bool) :
    d.probOf (reindex e ω)=d.probOf ω := by
  exact Equiv.prod_comp e (fun i => d.prob (ω i))

/-- Complete original `total_reindex` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_reindex (d : FinDist (Option Bool)) {n : ℕ}
    (e : Equiv.Perm (Fin n)) (f : (Fin n → Option Bool) → ℝ) :
    total d (fun ω => f (reindex e ω))=total d f := by
  calc
    _ = ∑ ω : Fin n → Option Bool,d.probOf (reindex e ω)*f (reindex e ω) := by
      simp only [total,prob_reindex]
    _ = _ := (reindex e).sum_comp (fun ω => d.probOf ω*f ω)

/-- Complete original `total_coordinate_ratio` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_coordinate_ratio (d : FinDist (Option Bool)) (n : ℕ) (i : Fin (n+1)) :
    total d (fun ω : Fin (n+1) → Option Bool => (hit (ω i) : ℝ)/(count ω : ℝ))=
      total d (fun ω : Fin (n+1) → Option Bool => (hit (ω 0) : ℝ)/(count ω : ℝ)) := by
  have h := total_reindex d (Equiv.swap (0 : Fin (n+1)) i)
    (fun ω : Fin (n+1) → Option Bool => (hit (ω 0) : ℝ)/(count ω : ℝ))
  have hc (ω : Fin (n+1) → Option Bool) :
      count (fun j => ω ((Equiv.swap (0 : Fin (n+1)) i) j))=count ω :=
    count_reindex (Equiv.swap (0 : Fin (n+1)) i) ω
  simpa only [reindex,Equiv.coe_fn_mk,Equiv.swap_apply_left,hc] using h

/-- Complete original `total_sum` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_sum (d : FinDist (Option Bool)) {n k : ℕ}
    (f : Fin k → (Fin n → Option Bool) → ℝ) :
    total d (fun ω => ∑ i,f i ω)=∑ i,total d (f i) := by
  unfold total
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Complete original `total_one` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem total_one (d : FinDist (Option Bool)) (n : ℕ) :
    total d (fun _ : Fin n → Option Bool => (1 : ℝ))=1 := by
  simpa only [total,mul_one] using d.sum_probOf n

/-- Complete original `conditional_head_ratio` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem conditional_head_ratio (p μ : ℝ) (c : ℕ) :
    (∑ r : Option Bool,weight p μ r*((hit r : ℝ)/((hit r+c : ℕ) : ℝ)))=
      p*(1/((c : ℝ)+1)) := by
  norm_num [Fintype.sum_option,Fintype.sum_bool,weight,hit,bitSign,Nat.add_comm 1 c]
  ring

/-- Complete original `head_ratio` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem head_ratio (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1) (n : ℕ) :
    total (law p μ hp hμ) (fun ω : Fin (n+1) → Option Bool => (hit (ω 0) : ℝ)/(count ω : ℝ))=
      p*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => 1/((count ω : ℝ)+1)) := by
  rw [total_cons_swapped]
  simp only [law_prob,Fin.cons_zero,count_cons,conditional_head_ratio]
  exact total_mul _ _ _

/-- Complete original `inverse_count_bound` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem inverse_count_bound (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1)
    (hpos : 0<p) (n : ℕ) :
    total (law p μ hp hμ) (fun ω : Fin n → Option Bool => 1/((count ω : ℝ)+1)) ≤
      1/(p*((n : ℝ)+1)) := by
  have hpoint (ω : Fin (n+1) → Option Bool) :
      (∑ i : Fin (n+1),(hit (ω i) : ℝ)/(count ω : ℝ)) ≤ 1 := by
    rw [← Finset.sum_div,← Nat.cast_sum]
    change (count ω : ℝ)/(count ω : ℝ) ≤ 1
    by_cases h : (count ω : ℝ)=0
    · simp [h]
    · rw [div_self h]
  have hsum := total_mono (law p μ hp hμ) _ _ hpoint
  rw [total_sum,total_one] at hsum
  simp_rw [total_coordinate_ratio (law p μ hp hμ) n,head_ratio] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one] at hsum
  apply (le_div_iff₀ (mul_pos hpos (by positivity : (0 : ℝ)<(n : ℝ)+1))).mpr
  nlinarith

/-- Complete original `scalar_pilot_risk` guarantee for `PartialAddressPilotScalar`; all source hypotheses and output obligations are retained. -/
theorem scalar_pilot_risk (p μ : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hμ : |μ| ≤ 1)
    (hpos : 0<p) (n : ℕ) :
    total (law p μ hp hμ) (fun ω : Fin n → Option Bool => (empirical ω-μ)^2) ≤
      2/(p*((n : ℝ)+1)) := by
  calc
    _ ≤ 2*total (law p μ hp hμ) (fun ω : Fin n → Option Bool => 1/((count ω : ℝ)+1)) :=
      empirical_risk_bound p μ hp hμ n
    _ ≤ _ := by
      have h := inverse_count_bound p μ hp hμ hpos n
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

#print axioms law
#print axioms count_cons
#print axioms centered_cons
#print axioms total_cons
#print axioms conditional_square
#print axioms total_cons_swapped
#print axioms law_prob
#print axioms conditional_count
#print axioms weighted_square
#print axioms total_add
#print axioms total_mul
#print axioms total_mono
#print axioms centered_sum
#print axioms empirical_risk_identity
#print axioms risk_expression_bound
#print axioms empirical_risk_bound
#print axioms count_reindex
#print axioms prob_reindex
#print axioms total_reindex
#print axioms total_coordinate_ratio
#print axioms total_sum
#print axioms total_one
#print axioms conditional_head_ratio
#print axioms head_ratio
#print axioms inverse_count_bound
#print axioms scalar_pilot_risk
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotScalar
