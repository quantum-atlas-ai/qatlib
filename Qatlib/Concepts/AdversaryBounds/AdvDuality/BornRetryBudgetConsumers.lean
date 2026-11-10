/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RetryBudgetCoupling
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.NoisyLeastSquaresConsumer
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped ENNReal BigOperators Classical

set_option autoImplicit false

universe u v w

variable {State : Type u} {Output : Type v}

noncomputable def bornRetry (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    PlannedRetry Unit Bool where
  Plan _ := Unit
  choose _ := PMF.pure ()
  cost _ _ := ⟨1, Nat.succ_pos 0⟩
  perform _ _ := (bornDistribution (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
      (normalized_applyGate hU (normalized_ket (0 : Fin 2)))).map
    (fun i => if i = 1 then some true else none)
  retry _ _ := ()

instance bornRetry_planFintype (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∀ s, Fintype ((bornRetry U hU).Plan s) :=
  fun _ => inferInstanceAs (Fintype Unit)

instance bornRetry_planUnique (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∀ s, Unique ((bornRetry U hU).Plan s) :=
  fun _ => inferInstanceAs (Unique Unit)

def bornRetryLabel (i : Fin 2) : Option Bool := if i = 1 then some true else none

@[simp] theorem bornRetryLabel_zero : bornRetryLabel 0 = none := by
  simp [bornRetryLabel]

@[simp] theorem bornRetryLabel_one : bornRetryLabel 1 = some true := by
  simp [bornRetryLabel]

theorem bornRetry_perform_true (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (bornRetry U hU).perform () () (some true)
      = ENNReal.ofReal (MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) := by
  let d : PMF (Fin 2) := bornDistribution (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
    (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
  have hps : MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} = BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 := by
    simp [MeasureProb]
  have h1 : d 1 = ENNReal.ofReal (MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) := by
    simp only [d, bornDistribution_apply, hps]
  change (d.map bornRetryLabel) (some true) = _
  rw [pmf_map_apply_eq, tsum_fintype, Fin.sum_univ_two]
  rw [bornRetryLabel_zero, PMF.pure_apply, if_neg (by simp), mul_zero]
  rw [bornRetryLabel_one, PMF.pure_apply, if_pos rfl, mul_one, h1, zero_add]

theorem bornRetry_perform_false (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (bornRetry U hU).perform () () (some false) = 0 := by
  let d : PMF (Fin 2) := bornDistribution (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
    (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
  change (d.map bornRetryLabel) (some false) = 0
  rw [pmf_map_apply_eq, tsum_fintype, Fin.sum_univ_two]
  rw [bornRetryLabel_zero, PMF.pure_apply, if_neg (by decide), mul_zero,
    bornRetryLabel_one, PMF.pure_apply, if_neg (by decide), mul_zero]
  simp

theorem bornProb_sum_fin_two (ψ : QState (Fin 2)) (hψ : Normalized ψ) :
    BornProb ψ 0 + BornProb ψ 1 = 1 := by
  have h : ∑ i : Fin 2, BornProb ψ i = 1 := hψ
  simpa using h

theorem bornRetry_perform_none (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (bornRetry U hU).perform () () (none)
      = ENNReal.ofReal (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) := by
  let d : PMF (Fin 2) := bornDistribution (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
    (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
  have hps : MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} = BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 := by
    simp [MeasureProb]
  have hsplit : BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 0 = 1 - BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 := by
    have h := bornProb_sum_fin_two (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
      (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
    linarith [bornProb_nonneg (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 0]
  have h0 : d 0 = ENNReal.ofReal (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) := by
    simp only [d, bornDistribution_apply, hsplit, hps]
  change (d.map bornRetryLabel) (none) = _
  rw [pmf_map_apply_eq, tsum_fintype, Fin.sum_univ_two]
  rw [bornRetryLabel_zero, PMF.pure_apply, if_pos rfl, mul_one]
  rw [bornRetryLabel_one, PMF.pure_apply, if_neg (by simp), mul_zero]
  rw [add_zero, h0]

theorem geom_sum_succ (r : ℝ) : ∀ n : ℕ,
    1 + r * (∑ k ∈ Finset.range n, r ^ k) = ∑ k ∈ Finset.range (n + 1), r ^ k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (∑ k ∈ Finset.range (n + 1), r ^ k)
        = (∑ k ∈ Finset.range n, r ^ k) + r ^ n := Finset.sum_range_succ _ _
    have h2 : (∑ k ∈ Finset.range (n + 2), r ^ k)
        = (∑ k ∈ Finset.range (n + 1), r ^ k) + r ^ (n + 1) := Finset.sum_range_succ _ _
    calc 1 + r * (∑ k ∈ Finset.range (n + 1), r ^ k)
        = 1 + r * ((∑ k ∈ Finset.range n, r ^ k) + r ^ n) := by rw [h1]
      _ = (1 + r * (∑ k ∈ Finset.range n, r ^ k)) + r ^ (n + 1) := by ring
      _ = (∑ k ∈ Finset.range (n + 1), r ^ k) + r ^ (n + 1) := by rw [ih]
      _ = ∑ k ∈ Finset.range (n + 2), r ^ k := h2.symm

theorem ennreal_ofReal_succ_sub {C r : ℕ} (hr : r ≤ C) :
    ENNReal.ofReal (C + 1 - r) = 1 + ENNReal.ofReal (C - r) := by
  have hr' : (r : ℝ) ≤ C := by exact_mod_cast hr
  have h : (C : ℝ) + 1 - r = 1 + ((C : ℝ) - r) := by linarith
  have h2 : ENNReal.ofReal (1 + ((C : ℝ) - r)) = 1 + ENNReal.ofReal ((C : ℝ) - r) := by
    rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_one]
  rw [h, h2]

theorem ennreal_mul_ofReal {a b : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]

theorem ennreal_ofReal_succ_sub' {C r : ℕ} (hr : r ≤ C) :
    ENNReal.ofReal ((C : ℝ) + 1 - r) = 1 + ((C - r : ℕ) : ℝ≥0∞) := by
  have hr' : (r : ℝ) ≤ C := by exact_mod_cast hr
  have hsub : ((C - r : ℕ) : ℝ) = (C : ℝ) - r := Nat.cast_sub hr
  have h : (C : ℝ) + 1 - r = 1 + ((C - r : ℕ) : ℝ) := by
    rw [hsub]
    linarith
  have h2 : ENNReal.ofReal (1 + ((C - r : ℕ) : ℝ)) = 1 + ((C - r : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by norm_num)
      (by positivity : (0 : ℝ) ≤ ((C - r : ℕ) : ℝ)), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [h, h2]

theorem ennreal_p_add (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
  rw [← (ENNReal.ofReal_add hp (by linarith)), show p + (1 - p) = 1 by ring, ENNReal.ofReal_one]

theorem ennreal_cost_step (p W : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hW : 0 ≤ W) :
    ENNReal.ofReal p + ENNReal.ofReal (1 - p) * (1 + ENNReal.ofReal W)
      = ENNReal.ofReal (1 + (1 - p) * W) := by
  have hmul' : ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 + W)
      = ENNReal.ofReal ((1 - p) * (1 + W)) := by
    rw [ENNReal.ofReal_mul (by linarith)]
  have hmul'' : ENNReal.ofReal (1 + W) = 1 + ENNReal.ofReal W := by
    rw [ENNReal.ofReal_add (by norm_num) hW, ENNReal.ofReal_one]
  calc ENNReal.ofReal p + ENNReal.ofReal (1 - p) * (1 + ENNReal.ofReal W)
      = ENNReal.ofReal p + ENNReal.ofReal ((1 - p) * (1 + W)) := by
        rw [← hmul'', hmul']
    _ = ENNReal.ofReal (p + ((1 - p) * (1 + W))) := by
        rw [← (ENNReal.ofReal_add hp (mul_nonneg (by linarith) (by linarith)))]
    _ = ENNReal.ofReal (1 + (1 - p) * W) := by
      congr 1
      ring

set_option maxHeartbeats 400000 in

theorem bornRetry_eval (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ∀ B : ℕ,
    (bornRetry U hU).eval B () (fun a _ => if a then 1 else 0) (fun _ => 0)
      = 1 - (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ B := by
  intro B
  induction B with
  | zero =>
    rw [PlannedRetry.eval]
    simp
  | succ B ih =>
    rw [PlannedRetry.eval]
    have hcost : ((bornRetry U hU).cost () () : ℕ) = 1 := rfl
    simp only [Fintype.sum_unique]
    show ((bornRetry U hU).choose () ()).toReal
        * (if ((bornRetry U hU).cost () () : ℕ) ≤ B + 1 then
            ∑ o : Option Bool, ((bornRetry U hU).perform () () o).toReal
              * (match o with
                | some a => (if a then 1 else 0)
                | none =>
                    (bornRetry U hU).eval B () (fun a _ => if a then 1 else 0) (fun _ => 0))
          else 0)
      = 1 - (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ (B + 1)
    rw [if_pos (by rw [hcost]; omega)]
    simp only [Fintype.sum_option, Fintype.sum_bool, reduceIte, Bool.false_eq_true, if_false,
      mul_zero, add_zero]
    rw [bornRetry_perform_true U hU, bornRetry_perform_none U hU]
    have hp : 0 ≤ MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} :=
        measureProb_nonneg _ _
    have h0 : 0 ≤ 1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} := by
      have h := bornProb_sum_fin_two (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0))
        (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
      have hps : MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} = BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 := by
        simp [MeasureProb]
      rw [← hps] at h
      linarith [bornProb_nonneg (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 0]
    simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal h0]
    have hchoose : (((bornRetry U hU).choose () () : ℝ≥0∞)).toReal = 1 := by
      show ((PMF.pure () : PMF Unit) () : ℝ≥0∞).toReal = 1
      rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one]
    simp only [hchoose, one_mul, mul_one]
    rw [ih]
    have h1 : (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
        * (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ B
        = (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ (B + 1) := by
      rw [pow_succ, mul_comm]
    calc (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
          * (1 - (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ B)
          + MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}
        = 1 - ((1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
            * (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ B) := by ring
      _ = 1 - (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ (B + 1) := by rw [h1]

theorem bornRetry_run_succ (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (B : ℕ) (hB : 1 ≤ B) :
    (bornRetry U hU).run B ()
      = PMF.bind ((bornRetry U hU).perform () ()) (fun o => match o with
        | some a => PMF.pure (some a, B - 1)
        | none => (bornRetry U hU).run (B - 1) ()) := by
  rw [PlannedRetry.run]
  have h1 : (bornRetry U hU).choose () = (PMF.pure () : PMF ((bornRetry U hU).Plan ())) := rfl
  rw [h1, PMF.pure_bind]
  simp only [show ((bornRetry U hU).cost () () : ℕ) = 1 from rfl, dif_pos hB]
  apply congrArg (fun (g : Option Bool → PMF (Option Bool × ℕ)) =>
    PMF.bind ((bornRetry U hU).perform () ()) g)
  funext o
  cases o <;> rfl

set_option maxHeartbeats 400000 in

theorem bornRetry_spend_shift (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (B : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((bornRetry U hU).run B ())
        (fun x => ((B + 1 - x.2 : ℕ) : ℝ≥0∞))
      = 1 + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost ((bornRetry U hU).costedRun B ()) := by
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      PlannedRetry.costedRun]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  refine (tsum_congr
    (f := fun x => (bornRetry U hU).run B () x * ((B + 1 - x.2 : ℕ) : ℝ≥0∞))
    (g := fun x => (bornRetry U hU).run B () x * 1
      + (bornRetry U hU).run B () x * ((B - x.2 : ℕ) : ℝ≥0∞))
    (fun x => ?_)).trans ?_
  · show (bornRetry U hU).run B () x * ((B + 1 - x.2 : ℕ) : ℝ≥0∞)
      = (bornRetry U hU).run B () x * 1
        + (bornRetry U hU).run B () x * ((B - x.2 : ℕ) : ℝ≥0∞)
    by_cases hx : (bornRetry U hU).run B () x = 0
    · simp [hx]
    · have hle := (PlannedRetry.run_remaining (K := bornRetry U hU) B () x
        ((PMF.mem_support_iff _ _).mpr hx)).1
      have hB : ((B + 1 - x.2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((B : ℝ) + 1 - x.2) := by
        rw [← (ENNReal.ofReal_natCast (B + 1 - x.2))]
        congr 2
        have hnat : B + 1 - x.2 = (B - x.2) + 1 := by omega
        rw [hnat, Nat.cast_add, Nat.cast_one, Nat.cast_sub hle]
        ring
      rw [hB, ennreal_ofReal_succ_sub' hle, mul_add]
  · rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

set_option maxHeartbeats 400000 in

theorem bornRetry_cost (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ∀ B : ℕ,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost ((bornRetry U hU).costedRun B ())
      = ENNReal.ofReal (∑ k ∈ Finset.range B,
          (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k) := by
  intro B
  induction B with
  | zero =>
    simp only [PlannedRetry.costedRun, PlannedRetry.run_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, PMF.pure_map, PMF.pure_apply, Nat.sub_zero,
      Finset.sum_range_zero, ENNReal.ofReal_zero, ite_mul]
    refine ENNReal.tsum_eq_zero.mpr fun a => ?_
    by_cases ha : a = (none, 0)
    · subst ha
      simp
    · simp [ha]
  | succ B ih =>
    have hp0 : BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 0 + BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 = 1 :=
      bornProb_sum_fin_two _ (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
    have hp1 : MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} ≤ 1 := by
      have hps : BornProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 1 = MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} := by
        simp [MeasureProb]
      linarith [bornProb_nonneg (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) 0]
    have hp : 0 ≤ MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1} :=
        measureProb_nonneg _ _
    have hle : 0 ≤ (B : ℝ) + 1 - B := by norm_num
    simp only [PlannedRetry.costedRun,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    have hone1 : ((B + 1 - B : ℕ) : ℝ≥0∞) = 1 := by
      have h : B + 1 - B = 1 := by omega
      rw [h]
      norm_num
    rw [bornRetry_run_succ U hU (B + 1) (by omega),
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype, Fintype.sum_option, Fintype.sum_bool,
      Nat.succ_sub_one]
    have hone : (∑' a : Option Bool × ℕ,
        ((PMF.pure (some true, B) : PMF (Option Bool × ℕ))) a
          * ((B + 1 - a.2 : ℕ) : ℝ≥0∞)) = 1 := by
      show (∑' b : Option Bool × ℕ, (fun a : Option Bool × ℕ =>
          ((PMF.pure (some true, B) : PMF (Option Bool × ℕ))) a
            * ((B + 1 - a.2 : ℕ) : ℝ≥0∞)) b) = 1
      have hc := tsum_eq_single_of _ _ (fun a ha => by
        show ((PMF.pure (some true, B) : PMF (Option Bool × ℕ))) a
            * ((B + 1 - a.2 : ℕ) : ℝ≥0∞) = 0
        rw [PMF.pure_apply, if_neg ha]
        simp)
      rw [hc]
      simp
    have hfalse : (∑' a : Option Bool × ℕ,
        ((PMF.pure (some false, B) : PMF (Option Bool × ℕ))) a
          * ((B + 1 - a.2 : ℕ) : ℝ≥0∞)) = 1 := by
      show (∑' b : Option Bool × ℕ, (fun a : Option Bool × ℕ =>
          ((PMF.pure (some false, B) : PMF (Option Bool × ℕ))) a
            * ((B + 1 - a.2 : ℕ) : ℝ≥0∞)) b) = 1
      have hc := tsum_eq_single_of _ _ (fun a ha => by
        show ((PMF.pure (some false, B) : PMF (Option Bool × ℕ))) a
            * ((B + 1 - a.2 : ℕ) : ℝ≥0∞) = 0
        rw [PMF.pure_apply, if_neg ha]
        simp)
      rw [hc]
      simp
    have hnone : (∑' a : Option Bool × ℕ, ((bornRetry U hU).run B ()) a
        * ((B + 1 - a.2 : ℕ) : ℝ≥0∞))
      = 1 + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost ((bornRetry U hU).costedRun B ()) := by
      exact bornRetry_spend_shift U hU B
    rw [hnone, hone, hfalse, bornRetry_perform_true U hU, bornRetry_perform_none U hU,
      bornRetry_perform_false U hU, mul_one, zero_mul, add_zero]
    rw [add_comm]
    rw [ih]
    rw [ennreal_cost_step _ _ hp hp1 (by positivity)]
    have hmul : ENNReal.ofReal ((1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
        * ∑ k ∈ Finset.range B, (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k)
      = ENNReal.ofReal (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
        * ENNReal.ofReal (∑ k ∈ Finset.range B,
          (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k) := by
      rw [ENNReal.ofReal_mul (by linarith)]
    have hadd : ENNReal.ofReal 1 + ENNReal.ofReal ((1 - MeasureProb
        (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
        * ∑ k ∈ Finset.range B, (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k)
      = ENNReal.ofReal (1 + (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
          * ∑ k ∈ Finset.range B, (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k) := by
      rw [ENNReal.ofReal_add (by norm_num)
        (by positivity : (0 : ℝ) ≤ (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1})
          * ∑ k ∈ Finset.range B, (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) ^ k)]
    rw [geom_sum_succ (1 - MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}) B]

theorem born_retry_actual_mass_and_cost (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (B : ℕ) :
    let p := MeasureProb (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket 0)) {1}
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((bornRetry U hU).run B ()) (fun x => x.1 = some true)
      = ENNReal.ofReal (1 - (1 - p) ^ B) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost ((bornRetry U hU).costedRun B ())
      = ∑ k ∈ Finset.range B, ENNReal.ofReal ((1 - p) ^ k) := by
  (try dsimp only)
  constructor
  · rw [PlannedRetry.run_event]
    simp
    rw [bornRetry_eval]
  · rw [bornRetry_cost]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun k _ => pow_nonneg
        (sub_nonneg.mpr (measureProb_le_one
          (normalized_applyGate hU (normalized_ket (0 : Fin 2)))
          ({(1 : Fin 2)} : Finset (Fin 2)))) k)]

theorem relabelGate_hadamard_apply (i j : Fin 2) :
    relabelGate boolEquivFin2 Hadamard i j
      = Hadamard (boolEquivFin2.symm i) (boolEquivFin2.symm j) := by
  show Matrix.reindex boolEquivFin2 boolEquivFin2 Hadamard i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem relabelGate_hadamard_apply_zero (i : Fin 2) :
    ApplyGate (relabelGate boolEquivFin2 Hadamard) (Qatlib.Foundations.PureStateMath.Ket 0) i = (Real.sqrt 2 : ℂ)⁻¹ := by
  have h : ∀ i : Fin 2,
      ApplyGate (relabelGate boolEquivFin2 Hadamard) (Qatlib.Foundations.PureStateMath.Ket 0) i = (Real.sqrt 2 : ℂ)⁻¹ := by
    intro i
    show (∑ j : Fin 2,
        relabelGate boolEquivFin2 Hadamard i j * Qatlib.Foundations.PureStateMath.Ket 0 j) = _
    rw [Fin.sum_univ_two]
    simp only [relabelGate_hadamard_apply]
    norm_num [Hadamard, Qatlib.Foundations.PureStateMath.Ket, boolEquivFin2]
  exact h i

theorem relabelGate_hadamard_measureProb :
    MeasureProb (ApplyGate (relabelGate boolEquivFin2 Hadamard) (Qatlib.Foundations.PureStateMath.Ket 0)) {1} = (1 / 2 : ℝ) := by
  rw [MeasureProb, Finset.sum_singleton, BornProb,
    relabelGate_hadamard_apply_zero]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem geom_half_le (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k) ≤ 2 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp; norm_num
  | succ n ih =>
    have h1 : (∑ k ∈ Finset.range (n + 2), (1 / 2 : ℝ) ^ k)
        = (∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k) + (1 / 2 : ℝ) ^ (n + 1) :=
      Finset.sum_range_succ _ _
    have hp : (1 / 2 : ℝ) ^ n = 2 * (1 / 2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      ring
    rw [show n + 1 + 1 = n + 2 by omega, h1]
    have hstep := add_le_add_right ih ((1 / 2 : ℝ) ^ (n + 1))
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_nonneg (by norm_num) _
    rw [hp] at hstep
    have hg : (∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k)
        ≤ 2 - 2 * (1 / 2 : ℝ) ^ (n + 1) := by linarith [hstep]
    linarith [hg, hpow]

theorem geom_half_sum_le_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) ≤ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := geom_half_le n
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
    linarith [hpow]

set_option linter.unusedVariables false in

theorem born_retry_hadamard_budget_consumer (B C : ℕ) (hBC : B ≤ C) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        ((bornRetry (relabelGate boolEquivFin2 Hadamard)
          (relabelGate_unitary boolEquivFin2 hadamard_unitary)).run B ())
        (fun x => x.1 = some true)
      = ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ B) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        ((bornRetry (relabelGate boolEquivFin2 Hadamard)
          (relabelGate_unitary boolEquivFin2 hadamard_unitary)).costedRun C ()) ≤ 2 := by
  obtain ⟨hm, _⟩ := born_retry_actual_mass_and_cost (relabelGate boolEquivFin2 Hadamard)
    (relabelGate_unitary boolEquivFin2 hadamard_unitary) B
  rw [relabelGate_hadamard_measureProb] at hm
  norm_num at hm
  obtain ⟨_, hc⟩ := born_retry_actual_mass_and_cost (relabelGate boolEquivFin2 Hadamard)
    (relabelGate_unitary boolEquivFin2 hadamard_unitary) C
  rw [relabelGate_hadamard_measureProb] at hc
  refine ⟨hm, ?_⟩
  rw [hc]
  norm_num
  have hconv : (∑ k ∈ Finset.range C, ENNReal.ofReal (1 / 2) ^ k)
      = ENNReal.ofReal (∑ k ∈ Finset.range C, (1 / 2 : ℝ) ^ k) := by
    have h1 := (ENNReal.ofReal_sum_of_nonneg (s := Finset.range C)
      (f := fun k => (1 / 2 : ℝ) ^ k) (fun k _ => pow_nonneg (by norm_num) k)).symm
    calc (∑ k ∈ Finset.range C, ENNReal.ofReal (1 / 2) ^ k)
        = ∑ k ∈ Finset.range C, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          refine Finset.sum_congr rfl fun k _ => by
            rw [(ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ)) k).symm]
      _ = ENNReal.ofReal (∑ k ∈ Finset.range C, (1 / 2 : ℝ) ^ k) := h1
  rw [hconv]
  norm_num
  exact geom_half_sum_le_two C

end Qatlib.Concepts.AdversaryBounds.AdvDuality
