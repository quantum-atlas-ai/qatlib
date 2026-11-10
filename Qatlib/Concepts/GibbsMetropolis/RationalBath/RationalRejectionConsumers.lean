/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalRejectionTermination
import Qatlib.Concepts.LchsSimulation.StaticLchs.CountedPlanSampling
set_option warningAsError false

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

private theorem rational_mean_le (N : ℕ) (w : Fin N → ℕ) (b : ℕ)
    (hb : weightTotal w ≤ 2^b) : rationalMeanComparisons w b ≤ (N : ℝ≥0∞) := by
  have hnum : (∑ j : Fin N, w j * (j.val+1)) + (2^b-weightTotal w)*N ≤ (2^b)*N := by
    have hsum : (∑ j : Fin N, w j * (j.val+1)) ≤ weightTotal w * N := by
      unfold weightTotal
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_left _ (by omega)
    calc (∑ j : Fin N, w j * (j.val+1)) + (2^b-weightTotal w)*N
        ≤ weightTotal w * N + (2^b-weightTotal w)*N := Nat.add_le_add_right hsum _
      _ = (2^b)*N := by rw [← Nat.add_mul, Nat.add_sub_of_le hb]
  unfold rationalMeanComparisons
  calc
    _ ≤ (((2^b)*N : ℕ) : ℝ≥0∞) / ((2^b : ℕ) : ℝ≥0∞) :=
      ENNReal.div_le_div (Nat.cast_le.mpr hnum) le_rfl
    _ = (N : ℝ≥0∞) := by
      rw [Nat.cast_mul, mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by simp)]

theorem rational_effective_truncation_consumer (N : ℕ) (w : Fin N → ℕ)
    (fuel : ℕ) (hW : 0 < weightTotal w) :
    let b := Nat.clog 2 (weightTotal w)
    weightTotal w ≤ 2^b ∧ rationalRejectMass w b ≤ 1/2 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel) (fun z => rejectionOutcome z.1 = Sum.inr ()) ≤ (1/2 : ℝ≥0∞)^fuel ∧
    (∀ j : Fin N, rationalTerminalMass w b j - Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
      (fun z => rejectionOutcome z.1 = Sum.inl j) =
      (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞)*(rationalRejectMass w b)^fuel) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w b fuel) (fun z => (rejectionBits z.1 : ℝ≥0∞)) ≤ (2*b : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w b fuel) (fun z => (rejectionComparisons z.1 : ℝ≥0∞)) ≤ (2*N : ℕ) ∧
    (∀ z ∈ (rationalRejectionRun w b fuel).support,
      rejectionBits z.1 ≤ b*fuel ∧ rejectionComparisons z.1 ≤ N*fuel) := by
  let b := Nat.clog 2 (weightTotal w)
  have hcut := finite_coin_effective_cutoff (weightTotal w) fuel hW
  have hb : weightTotal w ≤ 2^b := hcut.1
  have hq : rationalRejectMass w b ≤ 1/2 := hcut.2.1
  have hf := rational_finite_return_pending_and_first_stop N w b fuel hW hb
  have he := rational_finite_three_resource_expectations N w b fuel hW hb
  have htail : (∑ t ∈ Finset.range fuel, (rationalRejectMass w b)^t) ≤ 2 := by
    calc _ ≤ ∑ t ∈ Finset.range fuel, (1/2 : ℝ≥0∞)^t :=
        Finset.sum_le_sum fun t _ => ENNReal.pow_le_pow_left hq
      _ ≤ ∑' t : ℕ, (1/2 : ℝ≥0∞)^t := ENNReal.sum_le_tsum _
      _ = 2 := by norm_num [ENNReal.tsum_geometric]
  refine ⟨hb, hq, ?_, ?_, ?_, ?_, he.2.2.2⟩
  · rw [hf.1]
    exact ENNReal.pow_le_pow_left hq
  · intro j
    rw [(rational_unbounded_actual_first_stop_law N w b hW hb).2.2.1 j |>.2.1, hf.2.1 j]
    have hp : (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) ≠ ⊤ :=
      ne_of_lt (ENNReal.div_lt_top (by simp) (by positivity))
    rw [ENNReal.mul_sub (fun _ _ => hp), mul_one,
      ENNReal.sub_sub_cancel hp]
    exact mul_le_of_le_one_right' (pow_le_one₀ (by positivity) (hq.trans (by norm_num)))
  · rw [he.2.1]
    calc _ ≤ (b : ℝ≥0∞)*2 := mul_le_mul_right htail _
      _ = ((2*b : ℕ) : ℝ≥0∞) := by simp [mul_comm]
  · rw [he.2.2.1]
    calc _ ≤ (N : ℝ≥0∞)*2 := mul_le_mul' (rational_mean_le N w b hb) htail
      _ = ((2*N : ℕ) : ℝ≥0∞) := by simp [mul_comm]

theorem rational_one_two_three_actual_consumer :
    let w := (![1,2,3] : Fin 3 → ℕ)
    weightTotal w = 6 ∧ rationalRejectMass w 3 = 1/4 ∧
    (∀ fuel : ℕ,
      (∀ j : Fin 3, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w 3 fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j) =
        (w j : ℝ≥0∞)/6*(1-(1/4 : ℝ≥0∞)^fuel)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w 3 fuel) (fun z => rejectionOutcome z.1 = Sum.inr ()) = (1/4 : ℝ≥0∞)^fuel) ∧
    rationalTerminalMass w 3 0 = 1/6 ∧ rationalTerminalMass w 3 1 = 1/3 ∧ rationalTerminalMass w 3 2 = 1/2 ∧
    (∀ (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^3),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w 3 hW hb) (fun z => ((3*z.2 : ℕ) : ℝ≥0∞)) = 4 ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w 3 hW hb) (fun z => ((3*(z.2-1)+z.1.val+1 : ℕ) : ℝ≥0∞)) = 10/3) ∧
    (weightDecodeCounted w 0).1 = some 0 ∧ (weightDecodeCounted w 1).1 = some 1 ∧
    (weightDecodeCounted w 2).1 = some 1 ∧ (weightDecodeCounted w 3).1 = some 2 ∧
    (weightDecodeCounted w 5).1 = some 2 ∧ (weightDecodeCounted w 6).1 = none := by
  let w := (![1,2,3] : Fin 3 → ℕ)
  have ht : weightTotal w = 6 := by decide
  have hq : rationalRejectMass w 3 = 1/4 := by
    norm_num [rationalRejectMass, coinRejectMass, ht]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hW : 0 < weightTotal w := by omega
  have hb : weightTotal w ≤ 2^3 := by omega
  have hterm := (rational_unbounded_actual_first_stop_law 3 w 3 hW hb).2.2.1
  refine ⟨ht, hq, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · intro fuel
    have hf := rational_finite_return_pending_and_first_stop 3 w 3 fuel hW hb
    exact ⟨fun j => by simpa only [ht, hq] using! hf.2.1 j,
      by simpa only [hq] using hf.1⟩
  · simpa [ht, w] using (hterm 0).2.1
  · rw [(hterm 1).2.1, ht]
    change (2 : ℝ≥0∞)/6 = 1/3
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  · rw [(hterm 2).2.1, ht]
    change (3 : ℝ≥0∞)/6 = 1/2
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  · intro hW' hb'
    have he := rational_unbounded_expected_resources_and_limits 3 w 3 hW' hb'
    have hm : rationalMeanComparisons w 3 = 5/2 := by
      norm_num [rationalMeanComparisons, Fin.sum_univ_succ, w, ht]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
    have hden : 1-(1/4 : ℝ≥0∞) ≠ 0 :=
      ne_of_gt (tsub_pos_iff_lt.mpr (by norm_num))
    constructor
    · rw [he.2.1, hq]
      apply (ENNReal.toReal_eq_toReal_iff'
        (ne_of_lt (ENNReal.div_lt_top (by finiteness) hden)) (by finiteness)).mp
      norm_num [ENNReal.toReal_sub_of_le (by norm_num : (1/4 : ℝ≥0∞) ≤ 1) (by simp)]
    · rw [he.2.2.1, hq, hm]
      apply (ENNReal.toReal_eq_toReal_iff'
        (ne_of_lt (ENNReal.div_lt_top (by finiteness) hden)) (by finiteness)).mp
      norm_num [ENNReal.toReal_sub_of_le (by norm_num : (1/4 : ℝ≥0∞) ≤ 1) (by simp)]

noncomputable def rationalThenAttempt {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    {A : Type} (F : Fin N → CostedLaw A) : PMF (Option A × ℕ × ℕ × ℕ) :=
  PMF.bind (rationalRejectionRun w b fuel) fun z =>
    match z.1 with
    | .inl (j,B,D) => (F j).map fun y => (some y.1,B,D,y.2)
    | .inr (B,D) => PMF.pure (none,B,D,0)

noncomputable def rationalInfiniteThenAttempt {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    {A : Type} (F : Fin N → CostedLaw A) : PMF (A × ℕ × ℕ × ℕ) :=
  PMF.bind (rationalStopLaw w b hW hb) fun z =>
    (F z.1).map fun y => (y.1,b*z.2,N*(z.2-1)+z.1.val+1,y.2)

private theorem pmf_map_congr_on_support {X Y : Type} (p : PMF X) (f g : X → Y)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff _ _).mpr hx)]

private theorem map_runFor {X Y : Type} (k : Unit → PMF (Configuration Unit X))
    (l : Unit → PMF (Configuration Unit Y)) (f : X → Y)
    (hk : (k ()).map (Sum.map f id) = l ()) (fuel : ℕ) :
    ∀ c : Configuration Unit X,
    (runFor k fuel c).map (fun z => (Sum.map f id z.1,z.2)) =
      runFor l fuel (Sum.map f id c) := by
  induction fuel with
  | zero => intro c; simp [runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
  | succ fuel ih =>
    intro c
    cases c with
    | inl x => simp [Sum.map, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
    | inr u =>
      cases u
      have hsucc (j : Unit → PMF (Configuration Unit X)) :
          runFor j (fuel+1) (.inr ()) = (j ()).bind (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor j fuel c)) := by
        simp [runFor, tick, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_map,
            Function.comp_def]
      rw [hsucc]
      have hsucc' : runFor l (fuel+1) (.inr ()) =
          (l ()).bind (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor l fuel c)) := by
        simp [runFor, tick, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_map,
            Function.comp_def]
      change _ = runFor l (fuel+1) (.inr ())
      rw [hsucc', ← hk, PMF.bind_map, PMF.map_bind]
      congr 1
      funext c
      change ((runFor k fuel c).map (fun z => (z.1,1+z.2))).map
          (fun z => (Sum.map f id z.1,z.2)) = _
      rw [PMF.map_comp]
      have hi := congrArg (fun p => p.map (fun z => (z.1,1+z.2))) (ih c)
      simpa only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp,
          Function.comp_def] using hi

theorem rationalRejectionNext_ticket_transport {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) :
    (finiteCoinNext b (weightTotal w) ()).map (Sum.map (weightTicket w hW) id) =
      rationalRejectionNext w b () := by
  simp only [finiteCoinNext, rationalRejectionNext, PMF.map_comp, Function.comp_def]
  congr 1
  funext pair
  rcases pair with ⟨bits, bitCost⟩
  let u := (bitVecEquiv b bits).val
  by_cases hu : u < weightTotal w
  · have hd := (weighted_decoder_intervals_and_actual_cost N w).2.2.2.2 hW ⟨u,hu⟩
    change Sum.map (weightTicket w hW) id (coinStep b (weightTotal w) bits) =
      (match (weightDecodeCounted w u).1 with | some j => Sum.inl j | none => Sum.inr ())
    rw [hd]
    simp [coinStep, decodeBoundedBits, u, hu]
  · have hd := (weightDecodeCounted_none_iff w u).mpr (Nat.le_of_not_gt hu)
    change Sum.map (weightTicket w hW) id (coinStep b (weightTotal w) bits) =
      (match (weightDecodeCounted w u).1 with | some j => Sum.inl j | none => Sum.inr ())
    rw [hd]
    simp [coinStep, decodeBoundedBits, u, hu]

theorem rationalRejectionRun_ticket_transport {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) :
    (rationalRejectionRun w b fuel).map (fun z => (rejectionOutcome z.1,rejectionBits z.1)) =
      (finiteCoinRun b (weightTotal w) fuel).map
        (fun z => (Sum.map (weightTicket w hW) id z.1,z.2)) := by
  have hrun := map_runFor (finiteCoinNext b (weightTotal w)) (rationalRejectionNext w b)
    (weightTicket w hW) (rationalRejectionNext_ticket_transport w b hW) fuel (.inr ())
  have hproj := (rational_counted_run_projection_and_paths N w b fuel).1
  have hbits : (rationalRejectionRun w b fuel).map (fun z => (rejectionOutcome z.1,rejectionBits z.1)) =
      (rationalRejectionRun w b fuel).map (fun z => (rejectionOutcome z.1,b*z.2)) := by
    apply pmf_map_congr_on_support
    intro z hz
    rw [(rational_counted_run_projection_and_paths N w b fuel).2 z hz |>.2.1]
  rw [hbits]
  have hl := congrArg (fun p => p.map (fun z => (z.1,b*z.2))) hproj
  have hr := congrArg (fun p => p.map (fun z => (z.1,b*z.2))) hrun
  simpa only [finiteCoinRun, PMF.map_comp, Function.comp_def] using hl.trans hr.symm

private theorem map_point_mass {X Y : Type} (p : PMF X) (f : X → Y) (y : Y) :
    p.map f y = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => f x = y) := by
  simp only [PMF.map_apply, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  apply tsum_congr
  intro x
  by_cases h : f x = y
  · simp [h]
  · simp only [if_neg h, if_neg (Ne.symm h), mul_zero]

private theorem expectation_outcome {X : Type} {N : ℕ} (p : PMF X)
    (f : X → Configuration Unit (Fin N)) (v : Fin N → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => (f x).elim v (fun _ => 0)) =
      ∑ j : Fin N, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => f x = Sum.inl j) * v j := by
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map p f]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_sum_type', tsum_fintype]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, tsum_zero, add_zero, map_point_mass]

private theorem rationalThenAttempt_observable {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    {A : Type} (F : Fin N → CostedLaw A) (g : Option A × ℕ → ℝ≥0∞)
    (hg : g (none,0) = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalThenAttempt w b fuel F) (fun z => g (z.1,z.2.2.2)) =
      (1-(rationalRejectMass w b)^fuel) * ∑ j : Fin N,
        (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F j) (fun y => g (some y.1,y.2)) := by
  rw [rationalThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : (fun z : Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ =>
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (match z.1 with
        | .inl (j,B,D) => (F j).map fun y => (some y.1,B,D,y.2)
        | .inr (B,D) => PMF.pure (none,B,D,0)) (fun z => g (z.1,z.2.2.2))) =
      (fun z => (rejectionOutcome z.1).elim
        (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F j) (fun y => g (some y.1,y.2))) (fun _ => 0)) := by
    funext z
    rcases z with ⟨c,t⟩
    rcases c with ⟨j,B,D⟩ | ⟨B,D⟩
    · simp [rejectionOutcome, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    · simp [rejectionOutcome, hg]
  rw [hsplit, expectation_outcome]
  simp_rw [(rational_finite_return_pending_and_first_stop N w b fuel hW hb).2.1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rationalStopLaw_bucket_expectation {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) (f : Fin N → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w b hW hb) (fun z => f z.1) =
      ∑ j : Fin N, (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * f j := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_prod_type', tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  change (∑' t : ℕ, rationalStopLaw w b hW hb (j,t) * f j) = _
  rw [ENNReal.tsum_mul_right]
  have hm : (∑' t : ℕ, rationalStopLaw w b hW hb (j,t)) = rationalTerminalMass w b j := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp [rationalStopMass, rationalTerminalMass]
  rw [hm, (rational_unbounded_actual_first_stop_law N w b hW hb).2.2.1 j |>.2.1]

private theorem rationalThenAttempt_ticket_projection {N : ℕ} (w : Fin N → ℕ)
    (b fuel : ℕ) (hW : 0 < weightTotal w) {A : Type} (F : Fin N → CostedLaw A) :
    (rationalThenAttempt w b fuel F).map (fun z => (z.1,z.2.1,z.2.2.2)) =
      finiteCoinThenAttempt b (weightTotal w) fuel (fun u => F (weightTicket w hW u)) := by
  let cont : Configuration Unit (Fin N) × ℕ → PMF (Option A × ℕ × ℕ) := fun z =>
    match z.1 with
    | .inl j => (F j).map fun y => (some y.1,z.2,y.2)
    | .inr _ => PMF.pure (none,z.2,0)
  have heq : (rationalThenAttempt w b fuel F).map (fun z => (z.1,z.2.1,z.2.2.2)) =
      PMF.bind ((rationalRejectionRun w b fuel).map
        (fun z => (rejectionOutcome z.1,rejectionBits z.1))) cont := by
    rw [rationalThenAttempt, PMF.map_bind, PMF.bind_map]
    congr 1
    funext z
    rcases z with ⟨c,t⟩
    rcases c with ⟨j,B,D⟩ | ⟨B,D⟩ <;>
      simp [cont, rejectionOutcome, rejectionBits, PMF.map_comp, PMF.pure_map, Function.comp_def]
  rw [heq, rationalRejectionRun_ticket_transport w b fuel hW,
    PMF.bind_map, finiteCoinThenAttempt]
  congr 1
  funext z
  rcases z with ⟨c,B⟩
  cases c <;> rfl

theorem rational_counted_attempt_actual_consumer (N : ℕ) (w : Fin N → ℕ)
    (b fuel : ℕ) (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    (A : Type) (F : Fin N → CostedLaw A) (E : A → Prop) :
    (rationalThenAttempt w b fuel F).map (fun z => (z.1,z.2.1,z.2.2.2)) =
      finiteCoinThenAttempt b (weightTotal w) fuel (fun u => F (weightTicket w hW u)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalThenAttempt w b fuel F) (fun z => ∃ a, z.1=some a ∧ E a) =
      (1-(rationalRejectMass w b)^fuel) * ∑ j : Fin N,
        (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (F j) (fun z => E z.1) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalThenAttempt w b fuel F) (fun z => (z.2.2.2 : ℝ≥0∞)) =
      (1-(rationalRejectMass w b)^fuel) * ∑ j : Fin N,
        (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (F j) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalInfiniteThenAttempt w b hW hb F) (fun z => E z.1) =
      ∑ j : Fin N, (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (F j) (fun z => E z.1) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalInfiniteThenAttempt w b hW hb F) (fun z => (z.2.1 : ℝ≥0∞)) =
      (b : ℝ≥0∞)/(1-rationalRejectMass w b) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalInfiniteThenAttempt w b hW hb F) (fun z => (z.2.2.1 : ℝ≥0∞)) =
      rationalMeanComparisons w b/(1-rationalRejectMass w b) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalInfiniteThenAttempt w b hW hb F) (fun z => (z.2.2.2 : ℝ≥0∞)) =
      ∑ j : Fin N, (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (F j) := by
  have he := rational_unbounded_expected_resources_and_limits N w b hW hb
  refine ⟨rationalThenAttempt_ticket_projection w b fuel hW F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rationalThenAttempt_observable w b fuel hW hb F
      (fun z => @ite ℝ≥0∞ (∃ a, z.1 = some a ∧ E a)
        (Classical.propDecidable _) 1 0) (by simp)
    simpa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event] using h
  · exact rationalThenAttempt_observable w b fuel hW hb F (fun z => (z.2 : ℝ≥0∞)) (by simp)
  · unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [rationalInfiniteThenAttempt,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    exact rationalStopLaw_bucket_expectation w b hW hb
      (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (F j) (fun z => E z.1))
  · rw [rationalInfiniteThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    exact he.2.1
  · rw [rationalInfiniteThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    exact he.2.2.1
  · rw [rationalInfiniteThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    exact rationalStopLaw_bucket_expectation w b hW hb
        (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (F j))

end Qatlib.Concepts.GibbsMetropolis.RationalBath
