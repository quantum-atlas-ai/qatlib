/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedCoinTape
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedExecutionBudget

/-!
# Expected runtime of coin-tape machines

`TapeExpectedBPP` expresses almost-sure termination, polynomial expected transition count, and
bounded error for a fair coin-tape machine. The finite worst-path hypotheses imply these
unbounded-execution guarantees and a cutoff tail bound, providing a concrete randomized
computation model in the setting of [NielsenChuang2010].

The machine `movingGeometricTape` moves right on a false coin and halts with output true on a
true coin. Its survival and first-halting masses are computed explicitly, giving an unbounded
execution with expected time two.

## Main statements

* `coinTape_worst_path_expected`: derive expected time and cutoff bounds from finite worst-path
  halting.
* `worst_path_bpp_actual_expected_time_and_cutoff`: transfer `TapeInBPP` to `TapeExpectedBPP`.
* `moving_tape_geometric_actual_unbounded_consumer`: compute the geometric stopping law and
  expected time.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

/-- A language has a fair coin-tape decider with common halting states, almost-sure termination,
a polynomial bound on expected transition count, and correct-output mass at least two thirds
on every input. -/
def TapeExpectedBPP (L : List Bool → Prop) : Prop :=
  ∃ (q : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (c k : ℕ),
    (∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none)) ∧
    ∀ input : List Bool,
      let next := coinTapeKernel q M accept
      let cfg := coinTapeNormalize q M accept (Turing.TM0.init (input.map some))
      generalNeverMass next cfg = 0 ∧
      generalUnboundedTime next cfg ≤ ((c * input.length ^ k + c : ℕ) : ℝ≥0∞) ∧
      (2/3 : ℝ≥0∞) ≤ ∑' cost : ℕ, haltJoint next cfg
        (if L input then true else false) cost

/-- If every length-`T` coin tape halts and the correct-output probability is at least two
thirds, the induced kernel terminates almost surely with expected time at most `T`. Its
correct-output mass is at least two thirds and its pending mass at cutoff `F` is at most `T
/ (F + 1)`. -/
theorem coinTape_worst_path_expected (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (input : List Bool) (T : ℕ) (b : Bool)
    (_hcommon : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none))
    (hhalt : ∀ w : Fin T → Bool,
      (coinTapeRun M accept (input.map some) (List.ofFn w)).1 ≠ none)
    (hcorrect : 2/3 ≤ fairTapeSuccess M accept (input.map some) T b) :
    let next := coinTapeKernel q M accept
    let cfg := coinTapeNormalize q M accept (Turing.TM0.init (input.map some))
    generalNeverMass next cfg = 0 ∧ generalUnboundedTime next cfg ≤ (T : ℝ≥0∞) ∧
    (2/3 : ℝ≥0∞) ≤ ∑' k : ℕ, haltJoint next cfg b k ∧
    ∀ F : ℕ, generalPendingMass next cfg F ≤ (T : ℝ≥0∞) / (F+1 : ℝ≥0∞) := by
  (try dsimp only)
  have hb := general_zero_pending_budget _ _ T
    (coinTape_zero_pending q M accept input T hhalt)
  refine ⟨hb.1, hb.2, ?_, ?_⟩
  · calc
      (2/3 : ℝ≥0∞) = ENNReal.ofReal (2/3 : ℝ) := by simp [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ ENNReal.ofReal (fairTapeSuccess M accept (input.map some) T b) :=
        ENNReal.ofReal_le_ofReal hcorrect
      _ = ∑ k ∈ Finset.range (T+1), haltJoint (coinTapeKernel q M accept)
          (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))) b k :=
        (coinTape_success_mass q M accept input T b).symm
      _ ≤ _ := ENNReal.sum_le_tsum _
  · intro F
    exact (general_online_cutoff _ _ F).2.trans (ENNReal.div_le_div_right hb.2 _)

/-- Every language in `TapeInBPP` belongs to `TapeExpectedBPP`, and finite worst-path halting
yields the stated almost-sure termination, expected-time, correctness, and cutoff bounds. -/
theorem worst_path_bpp_actual_expected_time_and_cutoff :
    (∀ L : List Bool → Prop, TapeInBPP L → TapeExpectedBPP L) ∧
    (∀ (q : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
      (accept : Fin (q+1) → Bool) (input : List Bool) (T : ℕ) (b : Bool),
      (∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none)) →
      (∀ w : Fin T → Bool,
        (coinTapeRun M accept (input.map some) (List.ofFn w)).1 ≠ none) →
      2/3 ≤ fairTapeSuccess M accept (input.map some) T b →
      let next := coinTapeKernel q M accept
      let cfg := coinTapeNormalize q M accept (Turing.TM0.init (input.map some))
      generalNeverMass next cfg = 0 ∧ generalUnboundedTime next cfg ≤ (T : ℝ≥0∞) ∧
      (2/3 : ℝ≥0∞) ≤ ∑' k : ℕ, haltJoint next cfg b k ∧
      ∀ F : ℕ, generalPendingMass next cfg F ≤ (T : ℝ≥0∞)/(F+1 : ℝ≥0∞)) := by
  classical
  refine ⟨?_, coinTape_worst_path_expected⟩
  intro L h
  obtain ⟨q,M,accept,c,k,hcommon,hinput⟩ := h
  refine ⟨q,M,accept,c,k,hcommon,?_⟩
  intro input
  obtain ⟨hh,hc⟩ := hinput input
  exact ⟨(coinTape_worst_path_expected q M accept input _ _ hcommon hh hc).1,
    (coinTape_worst_path_expected q M accept input _ _ hcommon hh hc).2.1,
    (coinTape_worst_path_expected q M accept input _ _ hcommon hh hc).2.2.1⟩

/-- A two-state tape machine that moves right in state zero on a false coin and writes a blank
before entering the halting state on a true coin. -/
def movingGeometricTape (c : Bool) : Turing.TM0.Machine (Option Bool) (Fin 2) :=
  fun ql _ => if ql = 0 then
    if c then some (1, Turing.TM0.Stmt.write none)
    else some (0, Turing.TM0.Stmt.move Turing.Dir.right)
  else none

/-- Accept exactly control state one of the moving geometric tape machine. -/
def movingTapeAccept (ql : Fin 2) : Bool := decide (ql = 1)

/-- Move the tape head one cell to the right and set the control state to zero. -/
def movingTapeRight (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)) :
    Turing.TM0.Cfg (Option Bool) (Fin 2) :=
  ⟨0, cfg.Tape.move Turing.Dir.right⟩

/-- The two coin choices of `movingGeometricTape` have the same halting state-symbol pairs. -/
theorem movingGeometricTape_common (ql : Fin 2) (γ : Option Bool) :
    movingGeometricTape false ql γ = none ↔ movingGeometricTape true ql γ = none := by
  by_cases h : ql = 0 <;> simp [movingGeometricTape, h]

/-- A configuration in control state zero remains a running configuration under normalization
for the moving geometric machine. -/
private theorem moving_normalize (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) : coinTapeNormalize 1 movingGeometricTape movingTapeAccept cfg =
      Sum.inr cfg := by
  simp [coinTapeNormalize, coinHalt, movingGeometricTape, h]

/-- From control state zero, a true coin produces the terminal value true, while a false coin
continues at `movingTapeRight cfg`. -/
private theorem moving_selected (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) (c : Bool) :
    coinTapeSelected 1 movingGeometricTape movingTapeAccept cfg c =
      if c then Sum.inl true else Sum.inr (movingTapeRight cfg) := by
  cases c <;> simp [coinTapeSelected, TM0_step_apply, movingGeometricTape, h,
    TM0StmtApply, coinTapeNormalize, coinHalt, movingTapeAccept, movingTapeRight]

/-- The one-step kernel expectation from control state zero is the equal-weight average of the
terminal true value and the right-shifted continuation value. -/
private theorem moving_expectation (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) (f : (Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin 2)) → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (coinTapeKernel 1 movingGeometricTape movingTapeAccept cfg) f =
      (1/2 : ℝ≥0∞) * f (Sum.inl true) +
        (1/2 : ℝ≥0∞) * f (Sum.inr (movingTapeRight cfg)) := by
  simp only [coinTapeKernel, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
      moving_selected cfg h]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      Fintype.sum_bool]
  norm_num [PMF.bernoulli_apply]

/-- Starting in control state zero, the mass still pending after `T` kernel steps is `2⁻ᵀ`. -/
theorem moving_pending (T : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) :
    generalPendingMass (coinTapeKernel 1 movingGeometricTape movingTapeAccept)
      (Sum.inr cfg) T = (1/2 : ℝ≥0∞)^T := by
  induction T generalizing cfg with
  | zero =>
    simpa only [pow_zero] using!
      (finiteSurvival_zero_running (coinTapeKernel 1 movingGeometricTape movingTapeAccept) cfg)
  | succ T ih =>
    change finiteSurvival _ (T+1) (Sum.inr cfg) = _
    rw [finiteSurvival_succ_running, moving_expectation cfg h,
      finiteSurvival_halted]
    have hi : finiteSurvival (coinTapeKernel 1 movingGeometricTape movingTapeAccept) T
        (Sum.inr (movingTapeRight cfg)) = (1/2 : ℝ≥0∞)^T := ih (movingTapeRight cfg) rfl
    rw [hi]
    simp [pow_succ, mul_comm]

/-- No finite coin list produces output false when the moving geometric machine starts in
control state zero. -/
private theorem moving_no_false :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)), cfg.q = 0 →
      (coinTapeRunAux movingGeometricTape movingTapeAccept coins cfg).1 ≠ some false := by
  intro coins
  induction coins with
  | nil =>
    intro cfg h
    simp [coinTapeRunAux, coinHalt, movingGeometricTape, h]
  | cons c coins ih =>
    intro cfg h
    cases c with
    | false =>
      simpa [coinTapeRunAux, coinHalt, movingGeometricTape, h, TM0_step_apply,
        TM0StmtApply, Prod.map, movingTapeRight] using ih (movingTapeRight cfg) rfl
    | true =>
      have hh : coinHalt movingGeometricTape
          (⟨1, cfg.Tape.write none⟩ : Turing.TM0.Cfg (Option Bool) (Fin 2)) = true := by
        simp [coinHalt, movingGeometricTape]
      have hn : coinHalt movingGeometricTape cfg = false := by
        simp [coinHalt, movingGeometricTape, h]
      have hs : Turing.TM0.step (movingGeometricTape true) cfg =
          some ⟨1, cfg.Tape.write none⟩ := by
        simp [TM0_step_apply, movingGeometricTape, h, TM0StmtApply]
      rw [coinTapeRunAux_cons_of_step_some _ _ _ _ _ _ hn hs,
        coinTapeRunAux_of_coinHalt _ _ _ _ hh]
      simp [movingTapeAccept]

/-- The joint mass of halting with output false at any cost is zero from control state zero. -/
theorem moving_false_mass (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) (k : ℕ) :
    haltJoint (coinTapeKernel 1 movingGeometricTape movingTapeAccept) (Sum.inr cfg) false k = 0 := by
  unfold haltJoint
  rw [← moving_normalize cfg h, ← coinTape_observe_point, coinTape_observed_law, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro w
  apply if_neg
  intro he
  exact moving_no_false (List.ofFn w) cfg h (congrArg Prod.fst he.symm)

/-- For a costed law with Boolean terminal values, the terminal event at cost `k` is the sum of
the true and false point masses at that cost. -/
private theorem bool_first_stop_event {S : Type} (p : CostedLaw (Bool ⊕ S)) (k : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => (∃ b, z.1 = Sum.inl b) ∧ z.2 = k) =
      p (Sum.inl true,k) + p (Sum.inl false,k) := by
  classical
  rw [← event_point_mass p (Sum.inl true,k), ← event_point_mass p (Sum.inl false,k)]
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p _ + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p _
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  rintro ⟨c,j⟩
  cases c with
  | inl b => cases b <;> by_cases hj : j = k <;> simp [hj]
  | inr s => simp

/-- From control state zero, the joint mass of halting with output true at cost `k` is zero at
cost zero and `2⁻ᵏ` at positive costs. -/
theorem moving_true_mass (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2))
    (h : cfg.q = 0) (k : ℕ) :
    haltJoint (coinTapeKernel 1 movingGeometricTape movingTapeAccept) (Sum.inr cfg) true k =
      if k = 0 then 0 else (1/2 : ℝ≥0∞)^k := by
  cases k with
  | zero => exact Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution.runFor_point_halt_zero _ _ _ _
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    have hs := first_stop_mass_add (coinTapeKernel 1 movingGeometricTape movingTapeAccept)
      (k+1) (k+1) cfg (by omega) le_rfl
    rw [bool_first_stop_event] at hs
    change (haltJoint _ (Sum.inr cfg) true (k+1) + haltJoint _ (Sum.inr cfg) false (k+1)) +
      generalPendingMass _ (Sum.inr cfg) (k+1) = generalPendingMass _ (Sum.inr cfg) (k+1-1) at hs
    rw [moving_false_mass cfg h (k+1), add_zero,
      moving_pending (k+1) cfg h, Nat.add_sub_cancel, moving_pending k cfg h] at hs
    have hh : (1/2 : ℝ≥0∞)^(k+1) + (1/2 : ℝ≥0∞)^(k+1) = (1/2 : ℝ≥0∞)^k := by
      rw [pow_succ, ← mul_add]
      simp [ENNReal.inv_two_add_inv_two]
    exact WithTop.add_right_cancel (ENNReal.pow_ne_top (by simp) ) (hs.trans hh.symm)

/-- On every input, the moving geometric machine has survival mass `2⁻ᵀ`, true-halting mass
`2⁻ᵏ` at positive costs, and zero false-halting mass. It terminates almost surely and has
expected time two. -/
theorem moving_tape_geometric_actual_unbounded_consumer :
    ∀ input : List Bool,
      let accept := (fun ql : Fin 2 => decide (ql = 1))
      let next := coinTapeKernel 1 movingGeometricTape accept
      let cfg := coinTapeNormalize 1 movingGeometricTape accept (Turing.TM0.init (input.map some))
      (∀ T : ℕ, generalPendingMass next cfg T = (1/2 : ℝ≥0∞)^T) ∧
      (∀ k : ℕ, haltJoint next cfg true k = if k = 0 then 0 else (1/2 : ℝ≥0∞)^k) ∧
      (∀ k : ℕ, haltJoint next cfg false k = 0) ∧
      generalNeverMass next cfg = 0 ∧ generalUnboundedTime next cfg = 2 := by
  intro input
  (try dsimp only)
  change (∀ T : ℕ, generalPendingMass (coinTapeKernel 1 movingGeometricTape movingTapeAccept)
      (coinTapeNormalize 1 movingGeometricTape movingTapeAccept (Turing.TM0.init (input.map some))) T = _) ∧ _
  rw [moving_normalize _ rfl]
  refine ⟨fun T => moving_pending T _ rfl, fun k => moving_true_mass _ rfl k,
    fun k => moving_false_mass _ rfl k, ?_, ?_⟩
  · change (⨅ T, generalPendingMass (coinTapeKernel 1 movingGeometricTape movingTapeAccept)
      (Sum.inr (Turing.TM0.init (input.map some))) T) = 0
    simp_rw [moving_pending _ (Turing.TM0.init (input.map some)) rfl]
    exact iInf_pow_eq_zero_ennreal _ (by simp)
  · change (∑' T, generalPendingMass (coinTapeKernel 1 movingGeometricTape movingTapeAccept)
      (Sum.inr (Turing.TM0.init (input.map some))) T) = 2
    simp_rw [moving_pending _ (Turing.TM0.init (input.map some)) rfl]
    rw [geom_tsum_ennreal _ (by simp)]
    simp [ENNReal.one_sub_inv_two]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
