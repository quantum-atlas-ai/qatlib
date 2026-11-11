/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.UniformMatchedSampling

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Signed Record Decomposition

Signed Record Decomposition constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

/-- Construction for sign Law in the signed record decomposition model. -/
def signLaw (a : ℝ) (ha : |a| ≤ 1) : FinDist Bool where
  prob b := (1+recordSign b*a)/2
  nonneg b := by
    have hb := abs_le.mp ha
    cases b <;> simp only [recordSign, Bool.false_eq_true, ite_false, ite_true] <;> linarith
  sum_one := by simp only [Fintype.sum_bool, recordSign, Bool.false_eq_true, ite_false, ite_true]; ring

/-- Complete original `sign_law_mean` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem sign_law_mean (a : ℝ) (ha : |a| ≤ 1) : (signLaw a ha).expect recordSign=a := by
  simp only [FinDist.expect,signLaw,Fintype.sum_bool,recordSign,Bool.false_eq_true,ite_false,ite_true]
  ring

/-- Construction for paired Signs in the signed record decomposition model. -/
def pairedSigns (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : FinDist (Bool × Bool) where
  prob z := (signLaw a ha).prob z.1*(signLaw b hb).prob z.2
  nonneg z := mul_nonneg ((signLaw a ha).nonneg z.1) ((signLaw b hb).nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,(signLaw b hb).sum_one,mul_one]
    exact (signLaw a ha).sum_one

/-- Complete original `paired_sign_mean` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem paired_sign_mean (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    (pairedSigns a b ha hb).expect (fun z => recordSign z.1*recordSign z.2)=a*b := by
  calc
    _ = (signLaw a ha).expect recordSign*(signLaw b hb).expect recordSign := by
      unfold FinDist.expect pairedSigns
      rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [sign_law_mean,sign_law_mean]

/-- Complete original `paired_sign_mgf` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem paired_sign_mgf (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (t : ℝ) :
    (pairedSigns a b ha hb).expect (fun z => Real.exp
      (t*(recordSign z.1*recordSign z.2-a*b))) ≤ Real.exp (t^2/2) := by
  have hf (z : Bool × Bool) : recordSign z.1*recordSign z.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases z with ⟨x,y⟩
    cases x <;> cases y <;> norm_num [recordSign]
  have ht := finite_hoeffding_centered_mgf (Bool × Bool) (pairedSigns a b ha hb)
    (fun z => recordSign z.1*recordSign z.2) (-1) 1 t (by norm_num) hf
  have he : t^2*((1 : ℝ)-(-1))^2/8=t^2/2 := by ring
  rw [paired_sign_mean,he] at ht
  exact ht

/-- Construction for split Record Tuple in the signed record decomposition model. -/
def splitRecordTuple (S : Type) (n : ℕ) :
    (Fin n → S × Bool) ≃ ((Fin n → S) × (Fin n → Bool)) where
  toFun ω := (fun i => (ω i).1,fun i => (ω i).2)
  invFun z := fun i => (z.1 i,z.2 i)
  left_inv ω := by funext i; exact Prod.eta (ω i)
  right_inv z := by rcases z with ⟨J,Q⟩; rfl

variable {S : Type} [Fintype S] [Nonempty S]

/-- Construction for conditional Signs in the signed record decomposition model. -/
def conditionalSigns {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (J : Fin n → S) :
    FinDist (Fin n → Bool) := independentSampleLaw (fun i => signLaw (m (J i)) (hm (J i)))

/-- Complete original `signed_record_factors` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem signed_record_factors (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (x : S) (b : Bool) :
    (signedRecordLaw m hm).prob (x,b)=(uniformLaw S).prob x*(signLaw (m x) (hm x)).prob b := by
  change (1+recordSign b*m x)/(2*(Fintype.card S : ℝ))=
    (1/(Fintype.card S : ℝ))*((1+recordSign b*m x)/2)
  rw [div_mul_eq_div_div]
  ring

/-- Complete original `signed_cohort_factors` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem signed_cohort_factors {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (J : Fin n → S) (Q : Fin n → Bool) :
    (signedRecordLaw m hm).probOf (fun i => (J i,Q i))=
      (uniformLaw S).probOf J*(conditionalSigns m hm J).prob Q := by
  change (∏ i : Fin n, (signedRecordLaw m hm).prob (J i,Q i))=
    (∏ i : Fin n, (uniformLaw S).prob (J i))*(∏ i : Fin n, (signLaw (m (J i)) (hm (J i))).prob (Q i))
  simp_rw [signed_record_factors]
  exact Finset.prod_mul_distrib

/-- Complete original `signed_cohort_disintegration` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem signed_cohort_disintegration {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (F : (Fin n → S × Bool) → ℝ) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*F ω)=
      ∑ J : Fin n → S, (uniformLaw S).probOf J*
        (conditionalSigns m hm J).expect (fun Q => F (fun i => (J i,Q i))) := by
  rw [← (splitRecordTuple S n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ J : Fin n → S, ∑ Q : Fin n → Bool,
    (signedRecordLaw m hm).probOf (fun i => (J i,Q i))*F (fun i => (J i,Q i)))=_
  apply Finset.sum_congr rfl
  intro J _
  simp_rw [signed_cohort_factors]
  unfold FinDist.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  ring

/-- Complete original `signed_cohort_site_projection` guarantee for `SignedRecordDecomposition`; all source hypotheses and output obligations are retained. -/
theorem signed_cohort_site_projection {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (F : (Fin n → S) → ℝ) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*F (fun i => (ω i).1))=
      ∑ J : Fin n → S, (uniformLaw S).probOf J*F J := by
  rw [signed_cohort_disintegration]
  simp only [finite_expect_const]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_record_factors
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_cohort_factors
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_cohort_disintegration
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_cohort_site_projection
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.sign_law_mean
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.paired_sign_mean
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.paired_sign_mgf
