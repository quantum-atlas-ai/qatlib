/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.Amplification.TiedGroupBounds

/-!
# Charged clocks for minimum finding

`initCharge` and `chargedCallCost` assign natural initialization and Boolean-query costs to BBHT
calls. `chargedBBHTLaw` and `chargedRunClock` use these costs to define the duration of ranked
runs.

The module bounds the mean charged clock, chooses a timeout budget, and proves an explicit
square-root bound and asymptotic `O(sqrt N)` growth. The underlying search and minimum-finding
analyses are [BoyerEtAl1998] and [DurrHoyer1996].

## Main statements

* `charged_attainment_moment`: bounds the initial charged clock moment.
* `chargedBudget_le_sqrt`: gives an explicit square-root budget bound.
* `chargedBudget_isBigO_sqrt`: states the asymptotic square-root bound.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
/-- The natural ceiling of the binary logarithm, used as an initialization charge. -/
noncomputable def initCharge (N : ℕ) : ℕ := Nat.ceil (binaryLog N)

/-- The per-call initialization charge plus the terminal Boolean query count. -/
noncomputable def chargedCallCost (N : ℕ) (x : SearchTrace N) : ℕ :=
  initCharge N + TerminalBooleanQueries (ExponentialSizes N) x

/-- The ranked BBHT law whose duration is the charged call cost. -/
noncomputable def chargedBBHTLaw {N : ℕ} (e : Fin N ≃ Fin N) (_hN : 0 < N) :
    RankedCallLaw N (SearchTrace N) :=
  bbhtJointLaw e (fun x => (chargedCallCost N x : ℝ)) (fun _ => Nat.cast_nonneg _)

/-- The sum of charged call costs along a list of search traces. -/
noncomputable def chargedRunClock (N : ℕ) (xs : List (SearchTrace N)) : ℕ :=
  (xs.map (chargedCallCost N)).sum

/-- The charged mean budget, defined as four times `sourceMeanBudget`. -/
noncomputable def chargedMeanBudget (N : ℕ) : ℝ := 4 * sourceMeanBudget N

/-- The natural ceiling of twice the charged mean budget. -/
noncomputable def chargedBudget (N : ℕ) : ℕ := Nat.ceil (2 * chargedMeanBudget N)

/-- The real run clock of the charged law equals the cast of the natural charged run clock. -/
theorem chargedRunClock_eq_real {N : ℕ} (e : Fin N ≃ Fin N) (hN : 0 < N)
    (xs : List (SearchTrace N)) :
    (chargedBBHTLaw e hN).runClock xs = (chargedRunClock N xs : ℝ) := by
  induction xs with
  | nil => simp [RankedCallLaw.runClock, chargedRunClock]
  | cons x xs ih =>
    simp only [RankedCallLaw.runClock, chargedBBHTLaw, bbhtJointLaw, chargedRunClock,
      List.map_cons, List.sum_cons, Nat.cast_add]
    exact congrArg (fun q : ℝ => (chargedCallCost N x : ℝ) + q) ih

/-- The charged call has a duration moment bounded by four times the source call envelope. -/
theorem chargedBBHTLaw_moment {N : ℕ} (e : Fin N ≃ Fin N) (hN : 0 < N)
    (t : ℕ) (ht : 0 < t) (htN : t < N) :
    ∃ q : ℝ, HasSum (fun x => (chargedBBHTLaw e hN).mass t x *
      (chargedBBHTLaw e hN).duration x) q ∧ q ≤ 4 * sourceCallEnvelope N t := by
  have hc := rankMarked_card e t htN.le
  have h := search_terminal_boolean_cost (rankMarked e t) (by omega)
  generalize hM : Fintype.card (Fin N) = M at h
  have hMN : M = N := hM.symm.trans (Fintype.card_fin N)
  clear hM
  subst M
  rw [hc] at h
  obtain ⟨q,hq,_,hqb⟩ := h
  have hL : 0 ≤ binaryLog N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hN)) (Real.log_pos (by norm_num)).le
  have hceil : (initCharge N : ℝ) < binaryLog N + 1 := Nat.ceil_lt_add_one hL
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have htrN : (t : ℝ) ≤ N := by exact_mod_cast htN.le
  have hratio : 1 ≤ (N : ℝ) / t := (le_div_iff₀ htr).2 (by simpa only [one_mul] using! htrN)
  have hR : 1 ≤ Real.sqrt ((N : ℝ) / t) := by
    nlinarith [Real.sqrt_nonneg ((N : ℝ) / t),
      Real.sq_sqrt (show 0 ≤ (N : ℝ) / t by positivity)]
  refine ⟨(initCharge N : ℝ) + q,?_,?_⟩
  · have hs := ((bbht_prefix_law e t ht htN).1.mul_right (initCharge N : ℝ)).add hq
    convert! hs using 1
    · funext x
      simp only [chargedBBHTLaw, bbhtJointLaw,
        if_pos (show 0 < t ∧ t < N from ⟨ht,htN⟩), chargedCallCost, Nat.cast_add]
      ring
    · ring
  · have hD : sourceCallEnvelope N t =
        (9/2 : ℝ) * Real.sqrt ((N : ℝ)/t) + binaryLog N := by
      rw [sourceCallEnvelope, if_neg ht.ne', Real.sqrt_div (Nat.cast_nonneg N)]
      ring
    rw [hD]
    nlinarith

/-- The charged call envelope and average continuation potential are bounded by four times the
current threshold envelope. -/
private theorem charged_potential_step {N : ℕ} (skip : RankSkip N) (hN : 0 < N)
    (t : ℕ) (ht : 0 < t) (htN : t < N) :
    4 * sourceCallEnvelope N t +
      (∑ i : Fin N, if i.val < t then 4 * thresholdEnvelope (sourceCallEnvelope N) (skip.next i) else 0) /
        (t : ℝ) ≤ 4 * thresholdEnvelope (sourceCallEnvelope N) t := by
  have h := thresholdEnvelope_skip_step skip (sourceCallEnvelope N)
    (sourceCallEnvelope_scaled_mono N hN) t ht htN
  have hsum : (∑ i : Fin N, if i.val < t then 4 * thresholdEnvelope (sourceCallEnvelope N) (skip.next i) else 0) =
      4 * (∑ i : Fin N, if i.val < t then thresholdEnvelope (sourceCallEnvelope N) (skip.next i) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [hsum, mul_div_assoc]
  simpa only [mul_add] using! mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)

/-- The initial charged ranked run has a nonnegative clock moment bounded by `chargedMeanBudget
N`. -/
theorem charged_attainment_moment {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) :
    ∃ q : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
      (chargedBBHTLaw T.indexOfRank hN).initialMass T.skip x *
        (chargedBBHTLaw T.indexOfRank hN).runClock x.2) q ∧
      0 ≤ q ∧ q ≤ chargedMeanBudget N := by
  let D := sourceCallEnvelope N
  let V := thresholdEnvelope D
  have hV0 : (4 : ℝ) * V 0 = 0 := by
    dsimp [V,D]
    rw [thresholdEnvelope_zero _ (sourceCallEnvelope_zero N), mul_zero]
  obtain ⟨q,hq,hq0,hqb⟩ := (chargedBBHTLaw T.indexOfRank hN).initialClock_moment T.skip
    (fun t => 4 * D t) (fun t => 4 * V t) hV0
    (chargedBBHTLaw_moment T.indexOfRank hN) (charged_potential_step T.skip hN) hN
  refine ⟨q,hq,hq0,?_⟩
  have hmono := thresholdEnvelope_monotone D (sourceCallEnvelope_scaled_mono N hN)
  have hsum : (∑ i : Fin N, V (T.skip.next i)) ≤ ∑ i : Fin N, V i.val :=
    Finset.sum_le_sum (fun i _ => hmono (T.skip.le_rank i))
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  have heq : (∑ i : Fin N, V i.val) / (N : ℝ) =
      expectedTraceCost (fun r => D (r-1)) N := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [expectedTraceCost_succ]
    simp only [V, thresholdEnvelope, Nat.add_sub_cancel, Nat.cast_succ]
  rw [heq] at hd
  have hb : (∑ i : Fin N, V (T.skip.next i)) / (N : ℝ) ≤ sourceMeanBudget N :=
    hd.trans (sourceEnvelope_initial_bound N hN)
  rw [← Finset.mul_sum, mul_div_assoc] at hqb
  unfold chargedMeanBudget
  exact hqb.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4))

/-- The natural charged budget is at least twice the charged mean budget. -/
theorem chargedBudget_ge_twice_mean (N : ℕ) :
    2 * chargedMeanBudget N ≤ (chargedBudget N : ℝ) := Nat.le_ceil _

/-- The charged budget equals the natural ceiling of four times the source timeout. -/
theorem chargedBudget_eq_four_sourceTimeout (N : ℕ) :
    chargedBudget N = Nat.ceil (4 * sourceTimeout N) := by
  unfold chargedBudget chargedMeanBudget
  rw [sourceTimeout_eq_twice]
  congr 1
  ring

/-- The charged budget is positive for a nonempty table. -/
theorem chargedBudget_pos (N : ℕ) (hN : 0 < N) : 0 < chargedBudget N := by
  apply Nat.ceil_pos.mpr
  change 0 < 2 * (4 * sourceMeanBudget N)
  exact mul_pos (by norm_num) (mul_pos (by norm_num) (sourceMeanBudget_pos N hN))

/-- For positive `N`, the charged budget is bounded by the stated explicit constant times `sqrt
N`. -/
theorem chargedBudget_le_sqrt (N : ℕ) (hN : 0 < N) :
    (chargedBudget N : ℝ) ≤
      (4 * ((45/2 : ℝ) + (112/5 : ℝ) / (Real.log 2)^2) + 1) * Real.sqrt N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : 1 ≤ Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have ht : 0 ≤ 4 * sourceTimeout N := by
    rw [sourceTimeout_eq_twice]
    exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (sourceMeanBudget_pos N hN).le)
  have hceil := Nat.ceil_lt_add_one ht
  rw [chargedBudget_eq_four_sourceTimeout]
  have hb := sourceTimeout_le_sqrt N hN
  nlinarith

/-- The charged budget grows as `O(sqrt N)`. -/
theorem chargedBudget_isBigO_sqrt :
    Asymptotics.IsBigO Filter.atTop (fun N : ℕ => (chargedBudget N : ℝ))
      (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound
    (4 * ((45/2 : ℝ) + (112/5 : ℝ) / (Real.log 2)^2) + 1) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hnonneg : (0 : ℝ) ≤ (chargedBudget N : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))] using! chargedBudget_le_sqrt N hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
