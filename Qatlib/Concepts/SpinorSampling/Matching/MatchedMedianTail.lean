/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedUnconditionalTail

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Median Tail

Matched Median Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

/-- Complete original `median_exp_weight_bound` guarantee for `MatchedMedianTail`; all source hypotheses and output obligations are retained. -/
private theorem median_exp_weight_bound {X : Type} [Fintype X] [DecidableEq X]
    {K : ℕ} (p : FinDist X) (f : X → ℝ) (μ ε t : ℝ) (hK : 0<K) (ht : 0≤t) :
    p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-μ|) ≤
      (p.expect (fun x => if ε < |f x-μ| then Real.exp t else 1))^K /
        Real.exp (t*(K : ℝ)/2) := by
  classical
  let b := fun ω : Fin K → X => (Finset.univ.filter (fun i => ε < |f (ω i)-μ|)).card
  have hpoint (ω : Fin K → X) :
      (if ε < |rawBlockMedian f ω-μ| then (1 : ℝ) else 0) ≤
      Real.exp (t*(b ω : ℝ))/Real.exp (t*(K : ℝ)/2) := by
    by_cases h : ε < |rawBlockMedian f ω-μ|
    · rw [ite_eq_left h, le_div_iff₀ (Real.exp_pos _), one_mul]
      apply Real.exp_le_exp.mpr
      have hb := raw_median_bad_count f ω μ ε hK h
      have hn : K ≤ 2*b ω := by dsimp [b]; omega
      have hnR : (K : ℝ) ≤ 2*(b ω : ℝ) := by exact_mod_cast hn
      have hh : (K : ℝ)/2 ≤ (b ω : ℝ) := by linarith
      have hp := mul_le_mul_of_nonneg_left hh ht
      nlinarith only [hp]
    · rw [ite_eq_right h]
      positivity
  have hpow (ω : Fin K → X) : Real.exp (t*(b ω : ℝ)) =
      ∏ i : Fin K, if ε < |f (ω i)-μ| then Real.exp t else 1 := by
    calc
      _ = (Real.exp t)^(b ω) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ = _ := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hmoment : (∑ ω : Fin K → X, p.probOf ω * Real.exp (t*(b ω : ℝ))) =
      (p.expect (fun x => if ε < |f x-μ| then Real.exp t else 1))^K := by
    simp_rw [hpow]
    rw [p.expect_prod (fun (_ : Fin K) (x : X) => if ε < |f x-μ| then Real.exp t else 1)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, FinDist.expect]
  have hmass : p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-μ|) =
      ∑ ω : Fin K → X, p.probOf ω * (if ε < |rawBlockMedian f ω-μ| then (1 : ℝ) else 0) := by
    unfold FinDist.probEvent
    rw [Finset.sum_filter]
    simp only [mul_ite, mul_one, mul_zero]
  calc
    _ = _ := hmass
    _ ≤ ∑ ω : Fin K → X, p.probOf ω *
        (Real.exp (t*(b ω : ℝ))/Real.exp (t*(K : ℝ)/2)) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω)
        (Finset.prod_nonneg fun _ _ => p.nonneg _)
    _ = (∑ ω : Fin K → X, p.probOf ω * Real.exp (t*(b ω : ℝ))) /
        Real.exp (t*(K : ℝ)/2) := by simp only [mul_div_assoc, Finset.sum_div]
    _ = _ := by rw [hmoment]

/-- Complete original `finite_median_strong_exponential_tail` guarantee for `MatchedMedianTail`; all source hypotheses and output obligations are retained. -/
theorem finite_median_strong_exponential_tail {X : Type} [Fintype X] [DecidableEq X]
    {K : ℕ} (p : FinDist X) (f : X → ℝ) (μ ε x : ℝ) (hK : 0<K) (hx : 2048≤x)
    (hbad : finiteBadMass p f μ ε ≤ 6*Real.exp (-x/256)) :
    p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-μ|) ≤
      Real.exp (-(K : ℝ)*x/2048) := by
  classical
  let t : ℝ := x/512
  let q := p.expect (fun z => if ε < |f z-μ| then Real.exp t else 1)
  have ht : 0≤t := by dsimp [t]; linarith
  have hE : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hE4 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ)^4 := by norm_num
      _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) hE 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hminus : Real.exp (-4 : ℝ) ≤ 1/16 := by
    have hp : Real.exp (-4 : ℝ)*Real.exp 4=1 := by rw [← Real.exp_add]; norm_num
    have hm := mul_le_mul_of_nonneg_right hE4 (Real.exp_pos (-4 : ℝ)).le
    nlinarith
  have hsmall : Real.exp (-x/512) ≤ 1/16 :=
    (Real.exp_le_exp.mpr (by linarith : -x/512 ≤ (-4 : ℝ))).trans hminus
  have hq0 : 0≤q := finite_expect_nonneg _ _ (fun z => by split_ifs <;> positivity)
  have hq : q≤2 := by
    have hp (z : X) : (if ε < |f z-μ| then Real.exp t else 1) ≤
        1+Real.exp t*(if ε < |f z-μ| then (1 : ℝ) else 0) := by
      split_ifs <;> simp only [mul_one, mul_zero, add_zero] <;> linarith [Real.exp_pos t]
    calc
      _ ≤ p.expect (fun z => 1+Real.exp t*(if ε < |f z-μ| then (1 : ℝ) else 0)) :=
        finite_expect_mono _ _ _ hp
      _ = 1+Real.exp t*finiteBadMass p f μ ε := by
        rw [finite_expect_add, finite_expect_const, finite_expect_mul, finite_bad_indicator_mean]
      _ ≤ 1+Real.exp t*(6*Real.exp (-x/256)) :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hbad (Real.exp_pos _).le)
      _ = 1+6*Real.exp (-x/512) := by
        rw [show Real.exp t*(6*Real.exp (-x/256)) =
          6*(Real.exp t*Real.exp (-x/256)) by ring, ← Real.exp_add]
        have htarg : t+(-x/256) = -x/512 := by dsimp [t]; ring
        rw [htarg]
      _ ≤ 2 := by linarith
  have htwo : (2 : ℝ) ≤ Real.exp (x/2048) :=
    hE.trans (Real.exp_le_exp.mpr (by linarith : (1 : ℝ)≤x/2048))
  have hpow : q^K ≤ Real.exp ((K : ℝ)*x/2048) := by
    calc
      _ ≤ (2 : ℝ)^K := pow_le_pow_left₀ hq0 hq K
      _ ≤ (Real.exp (x/2048))^K := pow_le_pow_left₀ (by norm_num) htwo K
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmain := median_exp_weight_bound p f μ ε t hK ht
  change p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-μ|) ≤
    q^K/Real.exp (t*(K : ℝ)/2) at hmain
  calc
    _ ≤ q^K/Real.exp (t*(K : ℝ)/2) := hmain
    _ ≤ Real.exp ((K : ℝ)*x/2048)/Real.exp (t*(K : ℝ)/2) :=
      div_le_div_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; dsimp [t]; ring

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_saturated_median_tail` guarantee for `MatchedMedianTail`; all source hypotheses and output obligations are retained. -/
theorem signed_saturated_median_tail (τ : Equiv.Perm S) {K : ℕ} (hK : 0<K)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε≤1) (hx : 2048≤(Fintype.card S : ℝ)*ε^2) :
    (productLaw (cohortLaw (signedRecordLaw a ha) (Fintype.card S))
      (cohortLaw (signedRecordLaw b hb) (Fintype.card S))).probEvent
      (fun ω : Fin K → ((Fin (Fintype.card S) → S × Bool) × (Fin (Fintype.card S) → S × Bool)) =>
        ε < |(rawBlockMedianQ (fun z => matchedStatisticQ z.1 z.2 τ) ω : ℝ)-
          setAverage Finset.univ (fun x => a x*b (τ x))|) ≤
      Real.exp (-(K : ℝ)*(Fintype.card S : ℝ)*ε^2/2048) := by
  simp_rw [raw_block_median_cast]
  have hbad := signed_matched_unconditional_tail τ (Fintype.card S) (Fintype.card S)
    Fintype.card_pos Fintype.card_pos (le_refl _) (le_refl _) a b ha hb ε hε0 hε1
  have hM : (0 : ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
  have he : -(Fintype.card S : ℝ)*(Fintype.card S : ℝ)*ε^2 /
      (256*(Fintype.card S : ℝ)) = -((Fintype.card S : ℝ)*ε^2)/256 := by
    field_simp [ne_of_gt hM]
  rw [he] at hbad
  have hmain := finite_median_strong_exponential_tail
    (productLaw (cohortLaw (signedRecordLaw a ha) (Fintype.card S))
      (cohortLaw (signedRecordLaw b hb) (Fintype.card S)))
    (fun z => (matchedStatisticQ z.1 z.2 τ : ℝ))
    (setAverage Finset.univ (fun x => a x*b (τ x))) ε
    ((Fintype.card S : ℝ)*ε^2) hK hx hbad
  calc
    _ ≤ Real.exp (-(K : ℝ)*((Fintype.card S : ℝ)*ε^2)/2048) := hmain
    _ = _ := by congr 1; ring

/-- Complete original `signed_saturated_median_confidence` guarantee for `MatchedMedianTail`; all source hypotheses and output obligations are retained. -/
theorem signed_saturated_median_confidence (τ : Equiv.Perm S) {K : ℕ} (hK : 0<K)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1)
    (ε ρ : ℝ) (hε0 : 0<ε) (hε1 : ε≤1) (hρ : 0<ρ)
    (hx : 2048≤(Fintype.card S : ℝ)*ε^2)
    (hbudget : 2048*Real.log (1/ρ) ≤ (K : ℝ)*(Fintype.card S : ℝ)*ε^2) :
    (productLaw (cohortLaw (signedRecordLaw a ha) (Fintype.card S))
      (cohortLaw (signedRecordLaw b hb) (Fintype.card S))).probEvent
      (fun ω : Fin K → ((Fin (Fintype.card S) → S × Bool) × (Fin (Fintype.card S) → S × Bool)) =>
        ε < |(rawBlockMedianQ (fun z => matchedStatisticQ z.1 z.2 τ) ω : ℝ)-
          setAverage Finset.univ (fun x => a x*b (τ x))|) ≤ ρ := by
  have hlog : -(K : ℝ)*(Fintype.card S : ℝ)*ε^2/2048 ≤ Real.log ρ := by
    rw [one_div, Real.log_inv] at hbudget
    linarith
  exact (signed_saturated_median_tail τ hK a b ha hb ε hε0 hε1 hx).trans
    ((Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hρ))

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_median_strong_exponential_tail
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_saturated_median_tail
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_saturated_median_confidence
