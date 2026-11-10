/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralCostClock
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedTapeConsumers
import Mathlib.Analysis.SpecificLimits.Normed
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

def movingPrice (s : ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2)) : ℕ := s.1 + 1

def movingPriceSelect (s : ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2))
    (b : Bool) : Bool ⊕ (ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2)) :=
  match coinTapeSelected 1 movingGeometricTape movingTapeAccept s.2 b with
  | .inl o => .inl o
  | .inr t => .inr (s.1+1,t)

noncomputable def movingPriceNext (s : ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2)) :
    PMF (Bool ⊕ (ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2))) :=
  (PMF.bernoulli (1/2) (by norm_num)).map (movingPriceSelect s)

def movingPriceInit (input : List Bool) :
    Bool ⊕ (ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2)) :=
  .inr (0,Turing.TM0.init (input.map some))

def movingPriceTriangle (j : ℕ) : ℕ := j*(j+1)/2

theorem movingPrice_selected (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (hq : cfg.q = 0) (b : Bool) :
    coinTapeSelected 1 movingGeometricTape movingTapeAccept cfg b =
      if b then .inl true else .inr (movingTapeRight cfg) := by
  cases b <;> simp [coinTapeSelected, TM0_step_apply, movingGeometricTape, hq,
    TM0StmtApply, coinTapeNormalize, coinHalt, movingTapeAccept, movingTapeRight]

theorem movingPrice_expectation (m : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (hq : cfg.q = 0) (f : (Bool ⊕ (ℕ × Turing.TM0.Cfg (Option Bool) (Fin 2))) → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (movingPriceNext (m,cfg)) f =
      (1/2:ℝ≥0∞)*f (.inl true) +
      (1/2:ℝ≥0∞)*f (.inr (m+1,movingTapeRight cfg)) := by
  simp only [movingPriceNext, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      Fintype.sum_bool]
  norm_num [movingPriceSelect, movingPrice_selected cfg hq, PMF.bernoulli_apply]

def movingPriceBlock (m n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (m+i+1)

@[simp] theorem movingPriceBlock_zero (m : ℕ) : movingPriceBlock m 0 = 0 := by
  simp [movingPriceBlock]

@[simp] theorem movingPriceBlock_one (m : ℕ) : movingPriceBlock m 1 = m+1 := by
  simp [movingPriceBlock]

theorem movingPriceBlock_succ (m n : ℕ) :
    movingPriceBlock m (n+1) = (m+1) + movingPriceBlock (m+1) n := by
  simp only [movingPriceBlock, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have he : (fun i : ℕ => m+(i+1)+1) = (fun i : ℕ => (m+1)+i+1) := by
    funext i; omega
  rw [he]
  omega

theorem movingPriceBlock_lower (m n : ℕ) : n ≤ movingPriceBlock m n := by
  calc
    n = ∑ i ∈ Finset.range n, (1:ℕ) := by simp
    _ ≤ movingPriceBlock m n := Finset.sum_le_sum fun i hi => by omega

theorem movingPriceBlock_triangle (n : ℕ) : movingPriceBlock 0 n = movingPriceTriangle n := by
  have ht : movingPriceBlock 0 n = (∑ i ∈ Finset.range n, i) + n := by
    simp [movingPriceBlock, Finset.sum_add_distrib]
  have hs := Finset.sum_range_id_mul_two n
  have htwo : movingPriceBlock 0 n * 2 = n*(n+1) := by
    rw [ht]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel] at hs; nlinarith
  unfold movingPriceTriangle
  rw [← htwo, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem movingPrice_weighted_point (m n k : ℕ)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)) (hq : cfg.q = 0) (o : Bool) :
    weightedRunFor movingPriceNext movingPrice (n+1) (.inr (m,cfg)) (.inl o,k) =
      if m+1 ≤ k then
        (1/2:ℝ≥0∞)*(if o=true ∧ k=m+1 then 1 else 0) +
        (1/2:ℝ≥0∞)*weightedRunFor movingPriceNext movingPrice n
          (.inr (m+1,movingTapeRight cfg)) (.inl o,k-(m+1))
      else 0 := by
  rw [costClock_weighted_point]
  simp only [movingPrice]
  by_cases hfit : m+1 ≤ k
  · simp only [if_pos hfit]
    change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (movingPriceNext (m,cfg))
      (fun x => weightedRunFor movingPriceNext movingPrice n x (.inl o,k-(m+1))) = _
    rw [movingPrice_expectation m cfg hq]
    simp only [costClock_weighted_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply,
      Prod.mk.injEq, Sum.inl.injEq]
    have he : k-(m+1)=0 ↔ k=m+1 := by omega
    simp only [he]
  · simp only [if_neg hfit]

theorem movingPrice_weighted_false (m n k : ℕ)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)) (hq : cfg.q = 0) :
    weightedRunFor movingPriceNext movingPrice n (.inr (m,cfg)) (.inl false,k) = 0 := by
  induction n generalizing m cfg k with
  | zero => simp [weightedRunFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n ih =>
    rw [movingPrice_weighted_point m n k cfg hq false]
    have hi := ih (m+1) (k-(m+1)) (movingTapeRight cfg) rfl
    simp only [hi, Bool.false_eq_true, false_and, if_false, mul_zero, zero_add]
    split_ifs <;> rfl

theorem movingPrice_weighted_true (m n k : ℕ)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)) (hq : cfg.q = 0) :
    weightedRunFor movingPriceNext movingPrice n (.inr (m,cfg)) (.inl true,k) =
      ∑ j ∈ Finset.range n, if movingPriceBlock m (j+1)=k then (1/2:ℝ≥0∞)^(j+1) else 0 := by
  induction n generalizing m cfg k with
  | zero => simp [weightedRunFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ n ih =>
    rw [movingPrice_weighted_point m n k cfg hq true]
    by_cases hfit : m+1 ≤ k
    · rw [if_pos hfit, ih (m+1) (k-(m+1)) (movingTapeRight cfg) rfl]
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [Nat.zero_add, movingPriceBlock_one, true_and, pow_one,
        mul_ite, mul_one, mul_zero]
      have hfirst : (if k=m+1 then (1/2:ℝ≥0∞) else 0) =
          (if m+1=k then (1/2:ℝ≥0∞) else 0) := by
        by_cases hk : k=m+1 <;> simp [hk, eq_comm]
      rw [hfirst]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : movingPriceBlock (m+1) (j+1)=k-(m+1) ↔ movingPriceBlock m (j+2)=k := by
        have hb : movingPriceBlock m (j+2) = (m+1)+movingPriceBlock (m+1) (j+1) :=
          movingPriceBlock_succ m (j+1)
        rw [hb]
        omega
      simp only [he, pow_succ']
    · rw [if_neg hfit]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      apply if_neg
      intro he
      have hl : m+1 ≤ movingPriceBlock m (j+1) := by rw [movingPriceBlock_succ]; omega
      omega

theorem moving_price_actual_joint_triangular_charge : ∀ (input : List Bool) (k : ℕ),
    haltJoint (costClockNext movingPriceNext movingPrice)
      (costClockEmbed movingPrice (movingPriceInit input)) true k =
        (∑' j : ℕ, if movingPriceTriangle (j+1)=k then (1/2:ℝ≥0∞)^(j+1) else 0) ∧
    haltJoint (costClockNext movingPriceNext movingPrice)
      (costClockEmbed movingPrice (movingPriceInit input)) false k = 0 := by
  intro input k
  have hc : ∀ s, 1 ≤ movingPrice s := by intro s; simp [movingPrice]
  have ht := movingPrice_weighted_true 0 k k (Turing.TM0.init (input.map some)) rfl
  have hf := movingPrice_weighted_false 0 k k (Turing.TM0.init (input.map some)) rfl
  rw [cost_clock_arbitrary_configuration_halt_joint _ _ movingPriceNext movingPrice hc
    (movingPriceInit input) true k k le_rfl,
    cost_clock_arbitrary_configuration_halt_joint _ _ movingPriceNext movingPrice hc
    (movingPriceInit input) false k k le_rfl]
  refine ⟨?_, hf⟩
  change weightedRunFor movingPriceNext movingPrice k
    (.inr (0,Turing.TM0.init (input.map some))) (.inl true,k) = _
  rw [ht]
  simp only [movingPriceBlock_triangle]
  symm
  apply tsum_eq_sum
  intro j hj
  apply if_neg
  have hl : j+1 ≤ movingPriceTriangle (j+1) := by
    rw [← movingPriceBlock_triangle]
    exact movingPriceBlock_lower 0 (j+1)
  have hjk : k ≤ j := by have := Finset.mem_range.not.mp hj; omega
  omega

theorem movingPrice_pending (m n : ℕ)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)) (hq : cfg.q = 0) :
    generalPendingMass movingPriceNext (.inr (m,cfg)) n = (1/2:ℝ≥0∞)^n := by
  induction n generalizing m cfg with
  | zero => simpa only [pow_zero] using! finiteSurvival_zero_running movingPriceNext (m,cfg)
  | succ n ih =>
    change finiteSurvival movingPriceNext (n+1) (.inr (m,cfg)) = _
    rw [finiteSurvival_succ_running, movingPrice_expectation m cfg hq, finiteSurvival_halted]
    have hi : finiteSurvival movingPriceNext n (.inr (m+1,movingTapeRight cfg)) =
        (1/2:ℝ≥0∞)^n := ih (m+1) (movingTapeRight cfg) rfl
    rw [hi]
    simp [pow_succ, mul_comm]

theorem movingPrice_triangle_series :
    (∑' j : ℕ, (movingPriceTriangle (j+1) : ℝ≥0∞)*(1/2:ℝ≥0∞)^(j+1)) = 4 := by
  have ht (j : ℕ) : movingPriceTriangle (j+1) = (j+2).choose 2 := by
    rw [Nat.choose_two_right, show j+2-1 = j+1 by omega, Nat.mul_comm]
    rfl
  have hg : HasSum (fun j : ℕ => ((j+2).choose 2 : ℝ)*(1/2:ℝ)^j) 8 := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one 2 (r := (1/2:ℝ)) (by norm_num) using 1
    norm_num
  have hgr := hg.mul_right (1/2:ℝ)
  norm_num only [show (8:ℝ)*(1/2) = 4 by norm_num] at hgr
  have hs : HasSum (fun j : ℕ => (movingPriceTriangle (j+1):ℝ)*(1/2:ℝ)^(j+1)) 4 := by
    apply hgr.congr_fun
    intro j
    rw [ht, pow_succ]
    ring
  have he := ENNReal.ofReal_tsum_of_nonneg
    (show ∀ j : ℕ, 0 ≤ (movingPriceTriangle (j+1):ℝ)*(1/2:ℝ)^(j+1) by intro j; positivity)
    hs.summable
  rw [hs.tsum_eq] at he
  have hm (j : ℕ) : ENNReal.ofReal ((movingPriceTriangle (j+1):ℝ)*(1/2:ℝ)^(j+1)) =
      (movingPriceTriangle (j+1):ℝ≥0∞)*(1/2:ℝ≥0∞)^(j+1) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  simp_rw [hm] at he
  simpa using he.symm

theorem moving_price_native_tape_expected_charge_consumer : ∀ (input : List Bool),
    let next := costClockNext movingPriceNext movingPrice
    let cfg := costClockEmbed movingPrice (movingPriceInit input)
    generalNeverMass next cfg = 0 ∧ generalUnboundedTime next cfg = 4 ∧
    ∀ B : ℕ, generalPendingMass next cfg B ≤ 4/(B+1:ℝ≥0∞) ∧
      (1:ℝ≥0∞) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next B cfg)
        (fun z => z.1 = .inl true) + 4/(B+1:ℝ≥0∞) := by
  intro input
  let next := costClockNext movingPriceNext movingPrice
  let cfg := costClockEmbed movingPrice (movingPriceInit input)
  have hc : ∀ s, 1 ≤ movingPrice s := by intro s; simp [movingPrice]
  have hn0 : generalNeverMass movingPriceNext (movingPriceInit input) = 0 := by
    change (⨅ n,
        generalPendingMass movingPriceNext (.inr (0,Turing.TM0.init (input.map some))) n) = 0
    simp_rw [movingPrice_pending _ _ (Turing.TM0.init (input.map some)) rfl]
    exact iInf_pow_eq_zero_ennreal _ (by norm_num)
  have hn : generalNeverMass next cfg = 0 :=
    (cost_clock_nontermination_and_weighted_partition _ _ movingPriceNext movingPrice hc
      (movingPriceInit input)).1.trans hn0
  have hjt (k : ℕ) : haltJoint next cfg true k =
      ∑' j : ℕ, if movingPriceTriangle (j+1)=k then (1/2:ℝ≥0∞)^(j+1) else 0 :=
    (moving_price_actual_joint_triangular_charge input k).1
  have hjf (k : ℕ) : haltJoint next cfg false k = 0 :=
    (moving_price_actual_joint_triangular_charge input k).2
  have hseries : (∑' k : ℕ, (k:ℝ≥0∞)*haltJoint next cfg true k) = 4 := by
    simp_rw [hjt, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    have he : (∑' j : ℕ, ∑' k : ℕ, (k:ℝ≥0∞)*
        (if movingPriceTriangle (j+1)=k then (1/2:ℝ≥0∞)^(j+1) else 0)) =
        ∑' j : ℕ, (movingPriceTriangle (j+1):ℝ≥0∞)*(1/2:ℝ≥0∞)^(j+1) := by
      apply tsum_congr
      intro j
      simp only [mul_ite, mul_zero]
      rw [tsum_eq_single (movingPriceTriangle (j+1)) (fun k hk => by simp [Ne.symm hk])]
      simp only [if_true]
    rw [he, movingPrice_triangle_series]
  have htime : generalUnboundedTime next cfg = 4 := by
    have he := (general_unbounded_actual_expected_time _ _ next cfg).1
    simp only [hn, mul_zero, add_zero, tsum_fintype, Fintype.sum_bool] at he
    simp only [hjf, mul_zero, tsum_zero, add_zero] at he
    exact he.trans hseries
  have htrue : (∑' k : ℕ, haltJoint next cfg true k) = 1 := by
    have he := general_haltJoint_tsum_add_never next cfg
    simp only [hn, add_zero, tsum_fintype, Fintype.sum_bool] at he
    simpa only [hjf, tsum_zero, zero_add, add_zero] using he
  have hwtrue : (∑' k : ℕ, weightedRunFor movingPriceNext movingPrice k
      (movingPriceInit input) (.inl true,k)) = 1 := by
    dsimp only [next, cfg] at htrue
    simp only [cost_clock_arbitrary_configuration_halt_joint _ _ movingPriceNext movingPrice hc
      (movingPriceInit input) _ _ _ le_rfl] at htrue
    exact htrue
  refine ⟨hn, htime, ?_⟩
  intro B
  have hp := (cost_clock_expected_charge_and_online_cutoff _ _ movingPriceNext movingPrice hc
    (movingPriceInit input) B).2
  have he := cost_clock_arbitrary_output_event_cutoff _ _ movingPriceNext movingPrice hc
    (movingPriceInit input) B (fun o => o=true)
  have hev : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next B cfg) (fun z => ∃ o, z.1 = .inl o ∧ o=true) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next B cfg) (fun z => z.1 = .inl true) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (by intro z; simp)
  change generalPendingMass next cfg B ≤ generalUnboundedTime next cfg/(B+1:ℝ≥0∞) at hp
  rw [htime] at hp
  change _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (runFor next B cfg) _ + generalUnboundedTime next cfg/(B+1:ℝ≥0∞) at he
  rw [htime, hev] at he
  simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    add_zero, hwtrue] at he
  exact ⟨hp, he⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
