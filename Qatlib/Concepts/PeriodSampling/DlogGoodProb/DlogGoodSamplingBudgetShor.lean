/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodSamplingBudgetStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodOutputProbabilityShor
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogUniformGoodDivisibilityShor
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail

/-!
# Sampling budgets for good discrete-logarithm outcomes

Converts the good-output probability estimate into a bound for independent samples from the Born
distribution. An indicator-variance estimate yields `dlogGoodSamplingBudget`: a single-sample
probability of at least `1 / 480` and a one-half chance of collecting `t` good outputs in `1920
* 20 * t` trials, in the setting of [Shor1997].

## Main statements

* `dlog_fresh_good_count_budget`: Bounds the probability of obtaining enough successes.
* `dlogGoodSamplingBudget`: Establishes the Born-sampling budget contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Qatlib
open scoped Classical BigOperators

/-- For the stated normalized discrete-logarithm state and modulus window, a single Born sample
is good with probability at least `1 / 480`. -/
theorem dlog_good_sampling_single (p q r : ℕ) [NeZero p] (g x : ZMod p)
    (hprime : Nat.Prime p) (hp : 3 ≤ p) (hx : x ≠ 0) (hpq : p < q)
    (hg : orderOf g = p - 1) (hr : x = g ^ r) (hq : q ≤ 2 * (p - 1))
    (hnorm : Normalized (dlogTwoDimState p q g x)) :
    (dlogBornLaw p q g x hnorm).probEvent (L := 1)
      (fun ω => dlogGoodOutcome p q r (ω 0)) ≥ 1 / 480 := by
  rw [dlog_probEvent_one (dlogBornLaw p q g x hnorm) (dlogGoodOutcome p q r)]
  exact (dlogGoodOutputProbability p q r g x hprime hp hx hpq hg hr).2.2 hq

/-- The variance of an event indicator is at most its expectation. -/
private theorem indicator_variance_le {X : Type} [Fintype X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] :
    law.variance (fun x => if E x then (1 : ℝ) else 0) ≤
      law.expect (fun x => if E x then (1 : ℝ) else 0) := by
  let f := fun x => if E x then (1 : ℝ) else 0
  let μ := law.expect f
  have hsq (x : X) : f x ^ 2 = f x := by dsimp [f]; split_ifs <;> norm_num
  have he (x : X) : law.prob x * (f x - μ)^2 =
      law.prob x * f x - 2*μ*(law.prob x * f x) + μ^2*law.prob x := by
    calc
      _ = law.prob x * f x^2 - 2*μ*(law.prob x*f x) + μ^2*law.prob x := by ring
      _ = _ := by rw [hsq]
  have hv : law.variance f = μ-μ^2 := by
    change (∑ x, law.prob x * (f x-μ)^2) = _
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.mul_sum,← Finset.mul_sum,law.sum_one]
    change μ - 2*μ*μ + μ^2*1 = μ-μ^2
    ring
  change law.variance f ≤ μ
  rw [hv]
  nlinarith [sq_nonneg μ]

/-- If an event has single-sample mass at least `1 / 480`, then `1920 * 20 * t` independent
samples contain at least `t` successes with probability at least one half. -/
theorem dlog_fresh_good_count_budget {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E]
    (hmass : 1/480 ≤ law.expect (fun x => if E x then (1 : ℝ) else 0)) (t : ℕ) :
    law.probEvent (L := 1920*20*t)
      (fun ω => (t : ℝ) ≤ ∑ j, if E (ω j) then (1 : ℝ) else 0) ≥ 1/2 := by
  by_cases ht : t = 0
  · subst t
    simp only [Nat.mul_zero, Nat.cast_zero]
    have hfilter : (Finset.univ : Finset (Fin 0 → X)).filter
        (fun ω => (0 : ℝ) ≤ ∑ j, if E (ω j) then (1 : ℝ) else 0) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    rw [FinDist.probEvent, hfilter, law.sum_probOf 0]
    norm_num
  have htpos : 0 < t := by omega
  let L := 1920*20*t
  let f := fun x => if E x then (1 : ℝ) else 0
  let μ := law.expect f
  have hμ0 : 0 < μ := by dsimp [μ,f]; linarith
  have hL : 0 < L := by dsimp [L]; omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hLt : (L : ℝ) = 38400*(t : ℝ) := by dsimp [L]; push_cast; ring
  have hLge : (38400 : ℝ) ≤ L := by exact_mod_cast (show 38400 ≤ L by dsimp [L]; omega)
  have hμlo : 1/480 ≤ μ := hmass
  have hLμ : 80 ≤ (L : ℝ)*μ := by
    calc
      80 = (38400 : ℝ)*(1/480) := by norm_num
      _ ≤ _ := mul_le_mul hLge hμlo (by norm_num) (le_of_lt hLR)
  have hc := law.chebyshev_avg f hL (μ/2) (by linarith)
  have hc' : law.probEvent (L := L)
      (fun ω => μ/2 < |FinDist.avg f ω-μ|) ≤ 1/2 := by
    apply le_trans hc
    have hd : (0 : ℝ) < L*(μ/2)^2 := by positivity
    apply (div_le_iff₀ hd).2
    have hv := indicator_variance_le law E
    change law.variance f ≤ μ at hv
    have hm := mul_le_mul_of_nonneg_right hLμ (le_of_lt hμ0)
    nlinarith
  have hbad (ω : Fin L → X) (h : ¬((t : ℝ) ≤ ∑ j, f (ω j))) :
      μ/2 < |FinDist.avg f ω-μ| := by
    have hsum : (∑ j, f (ω j)) < t := lt_of_not_ge h
    have htarget : (t : ℝ) ≤ (L : ℝ)*(μ/2) := by
      rw [hLt]
      have htp : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      nlinarith [mul_nonneg htp (sub_nonneg.mpr hμlo)]
    have havg : FinDist.avg f ω < μ/2 :=
      (div_lt_iff₀ hLR).2 (hsum.trans_le (by simpa only [mul_comm] using! htarget))
    have hab := neg_le_abs (FinDist.avg f ω-μ)
    linarith
  have hmono : law.probEvent (L := L) (fun ω => ¬((t : ℝ) ≤ ∑ j, f (ω j))) ≤
      law.probEvent (L := L) (fun ω => μ/2 < |FinDist.avg f ω-μ|) := by
    simp only [FinDist.probEvent,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : ¬((t : ℝ) ≤ ∑ j, f (ω j))
    · simp only [if_pos h,if_pos (hbad ω h)]
      exact le_refl _
    · rw [if_neg h]
      split_ifs
      · exact Finset.prod_nonneg (fun i _ => law.nonneg (ω i))
      · exact le_refl _
  have hcomp := probEvent_compl law (fun ω : Fin L → X => (t : ℝ) ≤ ∑ j, f (ω j))
  change law.probEvent (L := L) (fun ω => (t : ℝ) ≤ ∑ j, f (ω j)) ≥ 1/2
  linarith [hmono.trans hc']

/-- Establishes the single-sample and repeated-sampling good-output budget for the
discrete-logarithm state associated with [Shor1997]. -/
theorem dlogGoodSamplingBudget : DlogGoodSamplingBudget := by
  intro p q r _ g x hprime hp hx hpq hg hr hq hnorm
  have hs := dlog_good_sampling_single p q r g x hprime hp hx hpq hg hr hq hnorm
  refine ⟨hs,?_⟩
  intro t
  apply dlog_fresh_good_count_budget (dlogBornLaw p q g x hnorm) (dlogGoodOutcome p q r) _ t
  rw [dlog_probEvent_one (dlogBornLaw p q g x hnorm) (dlogGoodOutcome p q r)] at hs
  simpa only [FinDist.expect,mul_ite,mul_one,mul_zero,Finset.sum_filter] using! hs

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
