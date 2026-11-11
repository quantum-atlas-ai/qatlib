/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.Concentration.SubsetProducts.FiniteMaclaurinBound
import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPooling

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Low Mean

Retained Bell Low Mean constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Construction for population Mean in the retained bell low mean model. -/
def populationMean (p : S → ℝ) : ℝ := (∑ x : S,p x)/(Fintype.card S : ℝ)

omit [DecidableEq S] in
/-- Complete original `bernoulli_subset_mean` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem bernoulli_subset_mean (p : S → ℝ) (hp : ∀ x,0≤p x ∧ p x≤1)
    (u : ℝ) (hu : 0≤u) (r : ℕ) :
    (1/(Fintype.card S).choose r : ℝ)*
      (∑ A ∈ (Finset.univ : Finset S).powersetCard r,∏ x ∈ A,(1+p x*(u-1)))≤
        (1+populationMean p*(u-1))^r := by
  have hg (x : S) : 0≤1+p x*(u-1) := by
    nlinarith [(hp x).2,mul_nonneg (hp x).1 hu]
  have hM : (Fintype.card S : ℝ)≠0 := by exact_mod_cast Fintype.card_pos.ne'
  have hs : (∑ x : S,(1+p x*(u-1)))=
      (Fintype.card S : ℝ)+(∑ x : S,p x)*(u-1) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Finset.sum_mul]
  have havg : (∑ x : S,(1+p x*(u-1)))/(Fintype.card S : ℝ)=
      1+populationMean p*(u-1) := by
    rw [hs]
    unfold populationMean
    field_simp
  have h := Maclaurin.subset_product_mean_bound (fun x => 1+p x*(u-1)) hg r
  rw [havg] at h
  exact h

omit [DecidableEq S] in
/-- Complete original `bernoulli_subset_poisson` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem bernoulli_subset_poisson (p : S → ℝ) (hp : ∀ x,0≤p x ∧ p x≤1)
    (u : ℝ) (hu : 0≤u) (r : ℕ) :
    (1/(Fintype.card S).choose r : ℝ)*
      (∑ A ∈ (Finset.univ : Finset S).powersetCard r,∏ x ∈ A,(1+p x*(u-1)))≤
        Real.exp ((r : ℝ)*populationMean p*(u-1)) := by
  have hμ : 0≤populationMean p :=
    div_nonneg (Finset.sum_nonneg fun x _ => (hp x).1) (Nat.cast_nonneg _)
  have hμ1 : populationMean p≤1 := by
    have hM : (0 : ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hM).mpr
    simpa only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      (Finset.sum_le_sum (fun x (_hx : x∈(Finset.univ : Finset S)) => (hp x).2))
  have hb : 0≤1+populationMean p*(u-1) := by nlinarith [mul_nonneg hμ hu]
  calc
    _ ≤ (1+populationMean p*(u-1))^r := bernoulli_subset_mean p hp u hu r
    _ ≤ (Real.exp (populationMean p*(u-1)))^r :=
      pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp (populationMean p*(u-1))]) r
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

variable {n m K : ℕ}

/-- Construction for bell Mean in the retained bell low mean model. -/
def bellMean (a b c k : S → ℝ) (τ : S → S) : ℝ :=
  populationMean (fun x => bellProbability (complexSpinor a b c k x) (complexSpinor a b c k (τ x)))

omit [DecidableEq S] [Nonempty S] in
/-- Complete original `bell_mean_nonneg` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem bell_mean_nonneg (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : S → S) : 0≤bellMean a b c k τ := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro x _
  exact (bell_probability_range _ _ (complex_spinor_mass a b c k hz x)
    (complex_spinor_mass a b c k hz (τ x))).1

/-- Complete original `matched_card_mass_nonneg` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem matched_card_mass_nonneg (τ : Equiv.Perm S) (r : ℕ) :
    0 ≤ matchedCardEventMass τ n m r := by
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg ((cohortLaw (uniformLaw S) n).nonneg z.1)
    ((cohortLaw (uniformLaw S) m).nonneg z.2)

/-- Complete original `observation_stratum_nonneg` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem observation_stratum_nonneg (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (r : ℕ) (u : ℝ) (hu : 0≤u) :
    0≤observationStratumPGF (n:=n) (m:=m) a b c k hz τ r u := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg ((cohortObservationLaw a b c k hz τ τ.injective).nonneg ω)
  change 0≤(if (matchedSites ω.1 ω.2.1 τ).card=r then u^(hitCount ω.2.2) else 0)
  split_ifs
  · exact pow_nonneg hu _
  · exact le_rfl

/-- Complete original `observation_stratum_poisson` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem observation_stratum_poisson (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (r : ℕ) (u : ℝ) (hu : 0≤u) :
    observationStratumPGF (n:=n) (m:=m) a b c k hz τ r u≤
      matchedCardEventMass τ n m r*Real.exp ((r : ℝ)*bellMean a b c k τ*(u-1)) := by
  have hp (x : S) : 0≤bellProbability (complexSpinor a b c k x)
      (complexSpinor a b c k (τ x)) ∧ bellProbability (complexSpinor a b c k x)
        (complexSpinor a b c k (τ x))≤1 := by
    have h := bell_probability_range _ _ (complex_spinor_mass a b c k hz x)
      (complex_spinor_mass a b c k hz (τ x))
    exact ⟨h.1,by linarith [h.2]⟩
  have h := bernoulli_subset_poisson _ hp u hu r
  have hD := mul_le_mul_of_nonneg_left h (matched_card_mass_nonneg (n:=n) (m:=m) τ r)
  rw [observation_stratum_pgf]
  simpa only [one_div,div_eq_mul_inv,mul_assoc,bellMean,one_mul] using hD

-- The actual pooled rational output, centered at the actual population mean.
-- This is still unnormalized, including every zero-probability R vector.
/-- Complete original `pooled_centered_low_mean_mgf` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem pooled_centered_low_mean_mgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (t : ℝ) :
    pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ (bellMean a b c k τ) t≤
      (∏ j : Fin K,matchedCardEventMass τ n m (ρ j))*
        Real.exp ((∑ j : Fin K,(ρ j : ℝ))*bellMean a b c k τ*(Real.exp t-1-t)) := by
  rw [pooled_centered_stratum_mgf,pooled_stratum_product]
  have hprod : (∏ j : Fin K,observationStratumPGF (n:=n) (m:=m) a b c k hz τ (ρ j) (Real.exp t))≤
      ∏ j : Fin K,matchedCardEventMass τ n m (ρ j)*
        Real.exp ((ρ j : ℝ)*bellMean a b c k τ*(Real.exp t-1)) := by
    apply Finset.prod_le_prod₀
    · intro j _
      exact observation_stratum_nonneg a b c k hz τ (ρ j) (Real.exp t) (Real.exp_pos t).le
    · intro j _
      exact observation_stratum_poisson a b c k hz τ (ρ j) (Real.exp t) (Real.exp_pos t).le
  apply (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans_eq
  rw [Finset.prod_mul_distrib,← Real.exp_sum]
  rw [← Finset.sum_mul,← Finset.sum_mul]
  rw [mul_left_comm,← Real.exp_add]
  congr 1
  congr 1
  ring


omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- Complete original `exp_remainder_le_square` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem exp_remainder_le_square (t : ℝ) (ht : |t|≤1) : Real.exp t-1-t≤t^2 := by
  have h := Real.exp_bound ht (n:=2) (by decide)
  norm_num [Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).2
  nlinarith [sq_nonneg t,sq_abs t]

/-- Complete original `pooled_centered_quadratic_mgf` guarantee for `RetainedBellLowMean`; all source hypotheses and output obligations are retained. -/
theorem pooled_centered_quadratic_mgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (t : ℝ) (ht : |t|≤1) :
    pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ (bellMean a b c k τ) t≤
      (∏ j : Fin K,matchedCardEventMass τ n m (ρ j))*
        Real.exp ((∑ j : Fin K,(ρ j : ℝ))*bellMean a b c k τ*t^2) := by
  apply (pooled_centered_low_mean_mgf a b c k hz τ ρ t).trans
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg fun j _ => matched_card_mass_nonneg (n:=n) (m:=m) τ (ρ j))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left (exp_remainder_le_square t ht)
  exact mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg (ρ j))
    (bell_mean_nonneg a b c k hz τ)

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bernoulli_subset_mean
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bernoulli_subset_poisson
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_stratum_poisson
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_centered_low_mean_mgf

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.exp_remainder_le_square
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_centered_quadratic_mgf
