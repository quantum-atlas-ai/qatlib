/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open scoped ENNReal BigOperators Classical

theorem amplification_clock_mass {Ω : Type*} (mass clock : Ω → ℝ)
    (hmass : HasSum mass 1) (hmnn : ∀ x, 0 ≤ mass x) (hcnn : ∀ x, 0 ≤ clock x)
    (q t : ℝ) (hq : HasSum (fun x => mass x * clock x) q) (ht : 0 < t) :
    ∃ p : ℝ, HasSum (fun x => if clock x ≤ t then mass x else 0) p ∧
      1-q/t ≤ p ∧ p ≤ 1 := by
  let good : Ω → ℝ := fun x => if clock x ≤ t then mass x else 0
  let bad : Ω → ℝ := fun x => if clock x ≤ t then 0 else mass x
  have hgood (x : Ω) : 0 ≤ good x ∧ good x ≤ mass x := by
    dsimp [good]; split_ifs <;> simp [hmnn x]
  have hbad (x : Ω) : 0 ≤ bad x ∧ bad x ≤ mass x := by
    dsimp [bad]; split_ifs <;> simp [hmnn x]
  have hg := Summable.of_nonneg_of_le (fun x => (hgood x).1)
    (fun x => (hgood x).2) hmass.summable
  have hb := Summable.of_nonneg_of_le (fun x => (hbad x).1)
    (fun x => (hbad x).2) hmass.summable
  have heq : (fun x => good x+bad x) = mass := by
    funext x; dsimp [good, bad]; split_ifs <;> ring
  have htotal : (∑' x, good x)+(∑' x, bad x)=1 := by
    have h := hg.hasSum.add hb.hasSum
    rw [heq] at h
    exact h.unique hmass
  have hpoint (x : Ω) : t*bad x ≤ mass x*clock x := by
    dsimp [bad]
    split_ifs with hx
    · simpa using! mul_nonneg (hmnn x) (hcnn x)
    · have h := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hx)) (hmnn x)
      nlinarith
  have hwb := hb.hasSum.mul_left t
  have hbound := Summable.tsum_le_tsum hpoint hwb.summable hq.summable
  rw [hwb.tsum_eq, hq.tsum_eq] at hbound
  have hbadbound : (∑' x, bad x) ≤ q/t := (le_div_iff₀ ht).mpr (by nlinarith)
  refine ⟨_, hg.hasSum, ?_, ?_⟩
  · linarith
  · have hbn : 0 ≤ (∑' x, bad x) := tsum_nonneg (fun x => (hbad x).1)
    linarith

theorem charged_initial_success_amplified {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    (1-1/((2*c : ℕ) : ℝ)) ≤ chargedInitialSuccess T (c*chargedBudget N) := by
  let ranked := SortedRankedTable.ofTable T
  let law := chargedBBHTLaw ranked.indexOfRank hN
  let B := c*chargedBudget N
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  have hbp : (0:ℝ) < chargedBudget N := by exact_mod_cast chargedBudget_pos N hN
  have ht : (0:ℝ) < B := by dsimp [B]; push_cast; positivity
  have hceil : 2*chargedMeanBudget N ≤ (chargedBudget N : ℝ) := chargedBudget_ge_twice_mean N
  obtain ⟨q, hq, _, hqb⟩ := charged_attainment_moment ranked hN
  obtain ⟨p, hp, hgood, _⟩ := amplification_clock_mass
    (law.initialMass ranked.skip) (fun x : Fin N × List (SearchTrace N) => law.runClock x.2)
    (law.initialMass_normalized ranked.skip hN).1
    (law.initialMass_normalized ranked.skip hN).2
    (fun x => law.runClock_nonneg x.2) q (B : ℝ) hq ht
  have hratio : q/(B : ℝ) ≤ 1/((2*c : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ ht (by positivity)]
    dsimp [B]
    push_cast
    have hm := mul_le_mul_of_nonneg_left hceil hcp.le
    have hqm := mul_le_mul_of_nonneg_left hqb (by positivity : 0 ≤ (2 : ℝ)*(c : ℝ))
    nlinarith
  have hgood' : 1-1/((2*c : ℕ) : ℝ) ≤ p := by linarith
  change HasSum (fun x : Fin N × List (SearchTrace N) =>
    if (chargedBBHTLaw ranked.indexOfRank hN).runClock x.2 ≤ (B : ℝ) then
      (chargedBBHTLaw ranked.indexOfRank hN).initialMass ranked.skip x else 0) p at hp
  simp only [chargedRunClock_eq_real, Nat.cast_le] at hp
  have heq := hp.unique (law.initial_completion_hasSum ranked.skip (chargedCallCost N) hN B)
  rw [heq] at hgood'
  have hsums := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    chargedCompletion_le_actual_success ranked hN i B)
  have hd := div_le_div_of_nonneg_right hsums (Nat.cast_nonneg N)
  rw [ranked.indexOfRank.sum_comp] at hd
  exact hgood'.trans hd

theorem amplifiedCombine_minimum_iff {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (a b : Fin N) :
    (∀ j, T (amplifiedCombine T a b) ≤ T j) ↔
      (∀ j, T a ≤ T j) ∨ (∀ j, T b ≤ T j) := by
  unfold amplifiedCombine
  by_cases h : T b < T a
  · rw [if_pos h]
    constructor
    · exact Or.inr
    · rintro (ha | hb)
      · intro j
        exact h.le.trans (ha j)
      · exact hb
  · rw [if_neg h]
    constructor
    · exact Or.inl
    · rintro (ha | hb)
      · exact ha
      · intro j
        exact (le_of_not_gt h).trans (hb j)

private theorem amplification_event_total {β : Type*} (p : PMF β) (E : β → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E+Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬E x)=1 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => 1) := by
      congr 1
      funext x
      by_cases hx : E x <;> simp [hx]
    _ = 1 := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const p 1

private theorem amplification_event_le_one {β : Type*} (p : PMF β) (E : β → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≤ 1 := by
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E+Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬E x) := le_self_add
    _ = 1 := amplification_event_total p E

theorem amplifiedStep_failure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (prev : PMF (Fin N × ℕ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedStep T hN prev) (fun x => ¬∀ j, T x.1 ≤ T j) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event prev (fun x => ¬∀ j, T x.1 ≤ T j)*
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN (chargedBudget N))
        (fun x => ¬∀ j, T x.1 ≤ T j) := by
  unfold amplifiedStep Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp_rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
    amplifiedCombine_minimum_iff, not_or]
  have he (p : Fin N × ℕ) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (chargedInitialPMF T hN (chargedBudget N))
        (fun f => if (¬∀ j, T p.1 ≤ T j) ∧ (¬∀ j, T f.1 ≤ T j) then 1 else 0) =
      (if (¬∀ j, T p.1 ≤ T j) then (1 : ℝ≥0∞) else 0)*
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (chargedInitialPMF T hN (chargedBudget N))
          (fun f => if (¬∀ j, T f.1 ≤ T j) then 1 else 0) := by
    by_cases hp : ∀ j, T p.1 ≤ T j <;> simp [hp]
  simp_rw [he]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [← ENNReal.tsum_mul_right]
  congr 1
  funext p
  by_cases hp : ∀ j, T p.1 ≤ T j <;> simp [hp]

theorem amplifiedMinimumPMF_failure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedMinimumPMF T hN c) (fun x => ¬∀ j, T x.1 ≤ T j) ≤
      (1/2 : ℝ≥0∞)^c := by
  have hf : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN (chargedBudget N))
      (fun x => ¬∀ j, T x.1 ≤ T j) ≤ (1/2 : ℝ≥0∞) := by
    let p := chargedInitialPMF T hN (chargedBudget N)
    let E : Fin N × ℕ → Prop := fun x => ∀ j, T x.1 ≤ T j
    have hsne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≠ ∞ :=
      ne_of_lt ((amplification_event_le_one p E).trans_lt (by simp))
    have hfne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬E x) ≠ ∞ :=
      ne_of_lt ((amplification_event_le_one p (fun x => ¬E x)).trans_lt (by simp))
    have htotal := congrArg ENNReal.toReal (amplification_event_total p E)
    rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at htotal
    have hhalf := (ENNReal.toReal_le_toReal (by norm_num) hsne).mpr
      (chargedInitialPMF_success_half T hN)
    norm_num at hhalf
    apply (ENNReal.toReal_le_toReal hfne (by norm_num)).mp
    norm_num
    linarith
  induction c with
  | zero =>
    simpa only [pow_zero] using! (amplification_event_le_one
      (amplifiedMinimumPMF T hN 0) (fun x => ¬∀ j, T x.1 ≤ T j))
  | succ c ih =>
    rw [amplifiedMinimumPMF, amplifiedStep_failure, pow_succ]
    exact mul_le_mul' ih hf

theorem amplifiedMinimumPMF_success {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    ENNReal.ofReal (1-(1/2 : ℝ)^c) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedMinimumPMF T hN c) (fun x => ∀ j, T x.1 ≤ T j) := by
  let p := amplifiedMinimumPMF T hN c
  let E : Fin N × ℕ → Prop := fun x => ∀ j, T x.1 ≤ T j
  have hsne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≠ ∞ :=
    ne_of_lt ((amplification_event_le_one p E).trans_lt (by simp))
  have hfne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬E x) ≠ ∞ :=
    ne_of_lt ((amplification_event_le_one p (fun x => ¬E x)).trans_lt (by simp))
  have htotal := congrArg ENNReal.toReal (amplification_event_total p E)
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at htotal
  have hfailure := (ENNReal.toReal_le_toReal hfne (by finiteness)).mpr
    (amplifiedMinimumPMF_failure T hN c)
  rw [ENNReal.toReal_pow] at hfailure
  norm_num at hfailure
  have hs :
      1-(1/2 : ℝ)^c ≤ (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E).toReal := by
        linarith
  have h := ENNReal.ofReal_le_ofReal hs
  rwa [ENNReal.ofReal_toReal hsne] at h

theorem finalRemarksAmplification : FinalRemarksAmplification := by
  intro N hN α inst T c hc
  exact ⟨amplifiedMinimumPMF_success T hN c, charged_initial_success_amplified T hN c hc⟩

end Qatlib.Concepts.AmplitudeSearch.Amplification
