/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.GeometricRetry
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

variable {O : Type} [Fintype O] [DecidableEq O]
variable (next : Unit → PMF ((O ⊕ Unit) × ℕ)) (price : ℕ)
variable (a : O → ℝ≥0∞) (q : ℝ≥0∞)
variable (ha : ∀ i, next () (Sum.inl i,price) = a i)
variable (hq : next () (Sum.inr (),price) = q)
variable (hs : ∀ cfg k, k ≠ price → next () (cfg,k) = 0)

include hs

omit [Fintype O] [DecidableEq O] in

theorem unitRestart_positive (hp : 0 < price) :
    ∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k := by
  intro s cfg k hm
  cases s
  by_cases hk : k = price
  · omega
  · exact False.elim (hm (hs cfg k hk))

include ha hq

theorem unitRestart_point (n k : ℕ) (i : O) :
    branchCostRun next (n+1) (Sum.inr ()) (Sum.inl i,k) =
      q*(if price ≤ k then branchCostRun next n (Sum.inr ()) (Sum.inl i,k-price) else 0) +
        (if price = k then a i else 0) := by
  rw [branchCostRun_point, tsum_prod_type', ENNReal.tsum_comm]
  have he : (∑' c : ℕ, ∑' cfg : O ⊕ Unit, next () (cfg,c) *
      (if c ≤ k then branchCostRun next n cfg (Sum.inl i,k-c) else 0)) =
      ∑' cfg : O ⊕ Unit, next () (cfg,price) *
        (if price ≤ k then branchCostRun next n cfg (Sum.inl i,k-price) else 0) := by
    apply tsum_eq_single price
    intro c hc
    simp only [hs _ c hc, zero_mul, tsum_zero]
  rw [he, tsum_sum_type', tsum_fintype, tsum_fintype]
  simp only [Fintype.sum_unique, ha, hq, branchCostRun_halted]
  by_cases hfit : price ≤ k
  · simp only [if_pos hfit, PMF.pure_apply, Prod.mk.injEq, Sum.inl.injEq]
    by_cases hk : price = k
    · subst k
      simp [mul_ite, add_comm]
    · have hn : k-price ≠ 0 := by omega
      simp [hn, hk]
  · have hn : price ≠ k := by omega
    simp [hfit,hn]

theorem unitRestart_below_price (n k : ℕ) (i : O) (hk : k < price) :
    branchCostRun next n (Sum.inr ()) (Sum.inl i,k) = 0 := by
  cases n with
  | zero => simp [branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n =>
    rw [unitRestart_point next price a q ha hq hs]
    simp [show ¬ price ≤ k by omega, show price ≠ k by omega]

theorem unitRestart_halt_recursion (hp : 0 < price) (k : ℕ) (i : O) :
    branchHaltJoint next (Sum.inr ()) i k =
      q*(if price ≤ k then branchHaltJoint next (Sum.inr ()) i (k-price) else 0) +
        (if price = k then a i else 0) := by
  have hpos := unitRestart_positive next price hs hp
  cases k with
  | zero =>
    simp [branchHaltJoint, branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply,
      show ¬ price ≤ 0 by omega, show price ≠ 0 by omega]
  | succ k =>
    unfold branchHaltJoint
    rw [unitRestart_point next price a q ha hq hs]
    by_cases hfit : price ≤ k+1
    · rw [if_pos hfit, if_pos hfit, branchCostRun_stable next hpos
        (Sum.inr ()) i (k+1-price) k (by omega)]
      rfl
    · rw [if_neg hfit, if_neg hfit]

theorem unitRestart_exact_receipt (hp : 0 < price) (r : ℕ) (i : O) :
    branchHaltJoint next (Sum.inr ()) i ((r+1)*price) = q^r*a i := by
  induction r with
  | zero =>
    simp only [Nat.zero_add, pow_zero, one_mul]
    rw [unitRestart_halt_recursion next price a q ha hq hs hp]
    have hz : branchHaltJoint next (Sum.inr ()) i 0 = 0 :=
      unitRestart_below_price next price a q ha hq hs 0 0 i hp
    simp [hz]
  | succ r ih =>
    rw [unitRestart_halt_recursion next price a q ha hq hs hp]
    have hfit : price ≤ (r+1+1)*price := by nlinarith
    have hne : price ≠ (r+1+1)*price := by nlinarith
    have he : (r+1+1)*price-price = (r+1)*price := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [if_pos hfit, if_neg hne, he, ih, add_zero, pow_succ']
    ring

theorem unitRestart_zero_address (i : O) (hi : a i = 0) (n k : ℕ) :
    branchCostRun next n (Sum.inr ()) (Sum.inl i,k) = 0 := by
  induction n generalizing k with
  | zero => simp [branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n ih => simp [unitRestart_point next price a q ha hq hs, ih, hi]

theorem unitRestart_support (hp : 0 < price) (i : O) (k : ℕ)
    (hm : branchHaltJoint next (Sum.inr ()) i k ≠ 0) :
    ∃ r : ℕ, k = (r+1)*price := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases he : price = k
    · exact ⟨0, by omega⟩
    · rw [unitRestart_halt_recursion next price a q ha hq hs hp k i,
        if_neg he, add_zero] at hm
      have hfit : price ≤ k := by by_contra hn; simp [hn] at hm
      rw [if_pos hfit] at hm
      obtain ⟨r,hr⟩ := ih (k-price) (by omega) (right_ne_zero_of_mul hm)
      exact ⟨r+1, by rw [Nat.add_mul, Nat.one_mul]; omega⟩

theorem unitRestart_total_halt (coin : PMF Bool)
    (hc : coin true = ∑ i, a i) (hf : coin false = q) (k : ℕ) :
    (∑ i, branchHaltJoint next (Sum.inr ()) i k) =
      branchHaltJoint (branchRetryNext coin price price) (Sum.inr ()) true k := by
  have he (n k : ℕ) : (∑ i, branchCostRun next n (Sum.inr ()) (Sum.inl i,k)) =
      branchCostRun (branchRetryNext coin price price) n (Sum.inr ()) (Sum.inl true,k) := by
    induction n generalizing k with
    | zero => simp [branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
    | succ n ih =>
      simp_rw [unitRestart_point next price a q ha hq hs]
      rw [branchRetry_point]
      simp only [true_and]
      by_cases hfit : price ≤ k
      · simp only [if_pos hfit, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [ih]
        by_cases hk : price = k <;> simp [hk,hc,hf]
      · have hk : price ≠ k := by omega
        simp [hfit,hk]
  exact he k k

theorem unitRestart_never_time_eq (coin : PMF Bool)
    (hc : coin true = ∑ i, a i) (hf : coin false = q) (hp : 0 < price) :
    generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ())) =
      generalNeverMass (branchClockNext (branchRetryNext coin price price))
        (branchClockEmbed (Sum.inr ())) ∧
    generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ())) =
      generalUnboundedTime (branchClockNext (branchRetryNext coin price price))
        (branchClockEmbed (Sum.inr ())) := by
  have hpos := unitRestart_positive next price hs hp
  have hbpos := branchRetry_positive coin price price hp hp
  have ht := unitRestart_total_halt next price a q ha hq hs coin hc hf
  have hz (k : ℕ) : branchHaltJoint (branchRetryNext coin price price)
      (Sum.inr ()) false k = 0 := branchRetry_false coin price price k k
  have ha' : (∑' i : O, ∑' k : ℕ, branchHaltJoint next (Sum.inr ()) i k) =
      ∑' k : ℕ, branchHaltJoint (branchRetryNext coin price price) (Sum.inr ()) true k := by
    rw [ENNReal.tsum_comm]
    simp only [tsum_fintype]
    exact tsum_congr ht
  have hn := (branch_cost_output_pending_never_conservation Unit O next hpos (Sum.inr ())).1
  have hbn := (branch_cost_output_pending_never_conservation Unit Bool
    (branchRetryNext coin price price) hbpos (Sum.inr ())).1
  rw [ha'] at hn
  rw [tsum_bool] at hbn
  simp only [hz, tsum_zero, zero_add] at hbn
  have hfinite : (∑' k : ℕ, branchHaltJoint (branchRetryNext coin price price)
      (Sum.inr ()) true k) ≠ ⊤ := by
    intro htop
    simp [htop] at hn
  have hnever := WithTop.add_left_cancel hfinite (hn.trans hbn.symm)
  refine ⟨hnever, ?_⟩
  have he := (general_unbounded_actual_expected_time (BranchClock Unit O) O
    (branchClockNext next) (branchClockEmbed (Sum.inr ()))).1
  have hbe := (general_unbounded_actual_expected_time (BranchClock Unit Bool) Bool
    (branchClockNext (branchRetryNext coin price price)) (branchClockEmbed (Sum.inr ()))).1
  simp_rw [branchClock_bridge next hpos] at he
  simp_rw [branchClock_bridge _ hbpos] at hbe
  rw [tsum_bool] at hbe
  simp only [hz, mul_zero, tsum_zero, zero_add] at hbe
  have hw : (∑' i : O, ∑' k : ℕ, (k : ℝ≥0∞)*branchHaltJoint next (Sum.inr ()) i k) =
      ∑' k : ℕ, (k : ℝ≥0∞)*branchHaltJoint
        (branchRetryNext coin price price) (Sum.inr ()) true k := by
    rw [ENNReal.tsum_comm]
    simp only [tsum_fintype, ← Finset.mul_sum, ht]
  rw [he,hbe,hw,hnever]

end Qatlib.Concepts.SearchStopping.PaidRestart
