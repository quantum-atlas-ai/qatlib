/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellLowMean

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Tail

Retained Bell Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

/-- Complete original `two_sided_exp_indicator` guarantee for `RetainedBellTail`; all source hypotheses and output obligations are retained. -/
theorem two_sided_exp_indicator (y s t : ℝ) (ht : 0≤t) :
    (if s< |y| then (1 : ℝ) else 0)≤
      Real.exp (-t*s)*(Real.exp (t*y)+Real.exp (-t*y)) := by
  by_cases h : s< |y|
  · rw [ite_eq_left h]
    by_cases hy : 0≤y
    · rw [abs_of_nonneg hy] at h
      have he := Real.one_le_exp (mul_nonneg ht (sub_nonneg.mpr h.le))
      have hp : Real.exp (t*(y-s))=Real.exp (-t*s)*Real.exp (t*y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hp] at he
      exact he.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le)
    · rw [abs_of_neg (lt_of_not_ge hy)] at h
      have he := Real.one_le_exp (mul_nonneg ht (sub_nonneg.mpr h.le))
      have hp : Real.exp (t*(-y-s))=Real.exp (-t*s)*Real.exp (-t*y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hp] at he
      exact he.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.exp_pos _).le) (Real.exp_pos _).le)
  · rw [ite_eq_right h]
    positivity

/-- Complete original `event_exp_chernoff` guarantee for `RetainedBellTail`; all source hypotheses and output obligations are retained. -/
theorem event_exp_chernoff {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) (f : X → ℝ) (s t : ℝ) (ht : 0≤t) :
    p.expect (fun x => if E x ∧ s< |f x| then 1 else 0)≤
      Real.exp (-t*s)*(p.expect (fun x => if E x then Real.exp (t*f x) else 0)+
        p.expect (fun x => if E x then Real.exp (-t*f x) else 0)) := by
  rw [← finite_expect_add,← finite_expect_mul]
  apply finite_expect_mono
  intro x
  by_cases hE : E x
  · simpa only [hE,true_and,ite_true] using two_sided_exp_indicator (f x) s t ht
  · simp [hE]

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m K : ℕ}

/-- Construction for pooled Stratum Bad Mass in the retained bell tail model. -/
def pooledStratumBadMass (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (ε : ℝ) : ℝ :=
  (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect (fun ω =>
    if observedRvec τ ω=ρ ∧ ε< |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)

/-- Complete original `pooled_stratum_bad_le_mass` guarantee for `RetainedBellTail`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_bad_le_mass (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (ε : ℝ) :
    pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
      ∏ j : Fin K,matchedCardEventMass τ n m (ρ j) := by
  rw [← pooled_stratum_at_one a b c k hz τ ρ]
  unfold pooledStratumBadMass pooledStratumPGF
  apply finite_expect_mono
  intro ω
  simp only [one_pow]
  split_ifs <;> simp_all

/-- Complete original `pooled_stratum_chernoff` guarantee for `RetainedBellTail`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_chernoff (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (ε t : ℝ) (ht : 0≤t) (hR : 0<∑ j : Fin K,(ρ j : ℝ)) :
    pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
      Real.exp (-t*(∑ j : Fin K,(ρ j : ℝ))*ε)*
        (pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ (bellMean a b c k τ) t+
          pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ (bellMean a b c k τ) (-t)) := by
  let p := freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K
  let E := fun ω : Fin K → CohortObservation n m τ => observedRvec τ ω=ρ
  let f := fun ω : Fin K → CohortObservation n m τ =>
    (pooledMatches τ ω : ℝ)*((pooledMeanQ τ ω : ℝ)-bellMean a b c k τ)
  have h := event_exp_chernoff p E f ((∑ j : Fin K,(ρ j : ℝ))*ε) t ht
  have hcmp : pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
      p.expect (fun ω => if E ω ∧ (∑ j : Fin K,(ρ j : ℝ))*ε< |f ω| then 1 else 0) := by
    apply finite_expect_mono
    intro ω
    by_cases hE : E ω
    · have heq : (pooledMatches τ ω : ℝ)=∑ j : Fin K,(ρ j : ℝ) := by
        simp only [pooledMatches,Nat.cast_sum]
        rw [hE]
      have hh : ε< |(pooledMeanQ τ ω : ℝ)-bellMean a b c k τ| ↔
          (∑ j : Fin K,(ρ j : ℝ))*ε< |f ω| := by
        dsimp [f]
        rw [abs_mul,heq,abs_of_pos hR]
        exact (mul_lt_mul_iff_right₀ hR).symm
      simp only [E,hE,true_and,hh]
      exact le_rfl
    · simp [E] at hE
      simp [E,hE]
  apply hcmp.trans
  convert h using 1
  · apply congrArg p.expect
    funext ω
    by_cases hE : E ω <;> simp [E,f,hE]
  · unfold pooledCenteredStratumMGF
    congr 1
    · congr 1
      ring
    · congr 1 <;> apply congrArg p.expect <;> funext ω <;>
        by_cases hE : E ω <;> simp [E,f,hE,mul_assoc]


-- No positive-stratum or positive-total-match promise is supplied as input.
-- Zero/small R remains in the right side through the actual event mass.
/-- Complete original `pooled_stratum_low_mean_tail` guarantee for `RetainedBellTail`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_low_mean_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (ε : ℝ) (hε : 0<ε) :
    pooledStratumBadMass (n:=n) (m:=m) a b c k hz τ ρ ε≤
      2*(∏ j : Fin K,matchedCardEventMass τ n m (ρ j))*
        Real.exp (-(∑ j : Fin K,(ρ j : ℝ))*ε^2/(4*(bellMean a b c k τ+ε))) := by
  let μ := bellMean a b c k τ
  let v := μ+ε
  let R := ∑ j : Fin K,(ρ j : ℝ)
  let D := ∏ j : Fin K,matchedCardEventMass τ n m (ρ j)
  have hμ : 0≤μ := bell_mean_nonneg a b c k hz τ
  have hv : 0<v := by dsimp [v]; linarith
  have hR0 : 0≤R := Finset.sum_nonneg fun j _ => Nat.cast_nonneg (ρ j)
  have hD0 : 0≤D := Finset.prod_nonneg fun j _ => matched_card_mass_nonneg (n:=n) (m:=m) τ (ρ j)
  change _≤2*D*Real.exp (-R*ε^2/(4*v))
  by_cases hR : 0<R
  · let t := ε/(2*v)
    have ht : 0<t := div_pos hε (mul_pos (by norm_num) hv)
    have ht2 : t≤1/2 := by
      change ε/(2*v)≤1/2
      apply (div_le_iff₀ (mul_pos (by norm_num) hv)).mpr
      dsimp [v]
      linarith
    have ht1 : |t|≤1 := by rw [abs_of_pos ht]; linarith
    have hp := pooled_centered_quadratic_mgf (n:=n) (m:=m) a b c k hz τ ρ t ht1
    have hn := pooled_centered_quadratic_mgf (n:=n) (m:=m) a b c k hz τ ρ (-t)
      (by simpa only [abs_neg] using ht1)
    simp only [neg_sq] at hn
    have hs : pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ μ t+
        pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ μ (-t)≤
          2*D*Real.exp (R*μ*t^2) := by linarith
    have hrate : μ*t^2-t*ε≤-ε^2/(4*v) := by
      calc
        _ ≤ v*t^2-t*ε := by
          have hh : 0≤v-μ := by dsimp [v]; linarith
          nlinarith [mul_nonneg hh (sq_nonneg t)]
        _ = _ := by dsimp [t]; field_simp; ring
    calc
      _ ≤ Real.exp (-t*R*ε)*
          (pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ μ t+
            pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ μ (-t)) :=
        pooled_stratum_chernoff a b c k hz τ ρ ε t ht.le hR
      _ ≤ Real.exp (-t*R*ε)*(2*D*Real.exp (R*μ*t^2)) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = 2*D*Real.exp (R*(μ*t^2-t*ε)) := by
        rw [mul_left_comm,← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hD0)
        apply Real.exp_le_exp.mpr
        convert mul_le_mul_of_nonneg_left hrate hR0 using 1
        ring
  · have hzR : R=0 := by linarith
    simp only [hzR,neg_zero,zero_mul,zero_div,Real.exp_zero,mul_one]
    exact (pooled_stratum_bad_le_mass a b c k hz τ ρ ε).trans (by linarith)

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.event_exp_chernoff
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_bad_le_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_chernoff

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_low_mean_tail
