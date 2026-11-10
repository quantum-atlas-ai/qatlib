/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Mathlib.Data.List.GetD
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

open Qatlib
open scoped ENNReal

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

@[simp] theorem compareFold_stable (xs : List (Bool × Bool)) (q : Fin 3) (hq : q ≠ 0) :
    xs.foldl compareUpdate q = q := by
  induction xs with
  | nil => rfl
  | cons ab xs ih => simpa only [List.foldl_cons, compareUpdate, if_neg hq] using! ih

theorem compareFold_less (xs : List (Bool × Bool)) :
    compareAccept (xs.foldl compareUpdate 0) = lexLess xs := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      rcases ab with ⟨a,b⟩
      simp only [compareAccept] at ih
      cases a <;> cases b <;> simp [List.foldl_cons, compareUpdate, lexLess, compareAccept,
        compareFold_stable, ih]

theorem binaryValue_lt (bs : List Bool) : binaryValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
      have hp := Nat.two_pow_pos bs.length
      cases b <;> simp only [binaryValue, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
        ↓reduceIte, zero_add] <;> omega

theorem lexLess_numeric (xs : List (Bool × Bool)) :
    lexLess xs = true ↔ binaryValue (xs.map Prod.fst) < binaryValue (xs.map Prod.snd) := by
  induction xs with
  | nil => simp [lexLess, binaryValue]
  | cons ab xs ih =>
      have ha := binaryValue_lt (xs.map Prod.fst)
      have hb := binaryValue_lt (xs.map Prod.snd)
      simp only [List.length_map] at ha hb
      rcases ab with ⟨a,b⟩
      cases a <;> cases b <;> simp [lexLess, binaryValue, ih, List.length_map] <;> omega

theorem pairedTape_head (l : List (Option (Bool × Bool))) (j : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ l)).head = l.getI j := by
  rw [Turing.Tape.move_right_n_head]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

theorem compare_after (xs : List (Bool × Bool)) (j : ℕ) (hj : j ≤ xs.length) :
    BitMachineAfter compareMachine (xs.map some) j =
      some ⟨(xs.take j).foldl compareUpdate 0,
        (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (xs.map some))⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj' : j ≤ xs.length := by omega
      have hjl : j < xs.length := by omega
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[j]
          (Turing.Tape.mk₁ (xs.map some))).head = some xs[j] := by
        rw [pairedTape_head, List.getI_eq_getElem _ (by simpa using! hjl)]
        simp [List.getElem_map]
      simp only [BitMachineAfter]
      rw [ih hj', Option.bind_some]
      rw [show Turing.TM0.step compareMachine
          ⟨(xs.take j).foldl compareUpdate 0,
            (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (xs.map some))⟩ =
          some ⟨compareUpdate ((xs.take j).foldl compareUpdate 0) xs[j],
            ((Turing.Tape.move Turing.Dir.right)^[j]
              (Turing.Tape.mk₁ (xs.map some))).move Turing.Dir.right⟩ from
        TM0_step_eq_some compareMachine _ _ _ (by
          rw [show (⟨(xs.take j).foldl compareUpdate 0,
            (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (xs.map some))⟩ :
            Turing.TM0.Cfg (Option (Bool × Bool)) (Fin 3)).Tape.head = some xs[j] from hhead]
          rfl)]
      congr 1
      congr 1
      · rw [List.take_succ_eq_append_getElem hjl, List.foldl_append]
        rfl
      · rw [Function.iterate_succ_apply']

theorem compare_correct (xs : List (Bool × Bool)) :
    tapeDecision compareMachine compareAccept (xs.map some) xs.length =
      some (decide (binaryValue (xs.map Prod.fst) < binaryValue (xs.map Prod.snd))) := by
  let T := (Turing.Tape.move Turing.Dir.right)^[xs.length] (Turing.Tape.mk₁ (xs.map some))
  have hhead : T.head = none := by
    rw [pairedTape_head, List.getI_eq_default _ (by simp)]
    rfl
  have hs : Turing.TM0.step compareMachine ⟨(xs.take xs.length).foldl compareUpdate 0,T⟩ = none := by
    rw [TM0_step_eq_none]
    change compareMachine _ T.head = none
    rw [hhead]
    rfl
  have hnum : lexLess xs = decide (binaryValue (xs.map Prod.fst) < binaryValue (xs.map Prod.snd)) := by
    apply Bool.eq_iff_iff.mpr
    simpa using! lexLess_numeric xs
  rw [clocked_tape_decision_halt_and_timeout]
  refine ⟨xs.length, ⟨(xs.take xs.length).foldl compareUpdate 0,T⟩, le_rfl,
    compare_after xs xs.length le_rfl, hs, ?_⟩
  simpa only [List.take_length] using! (compareFold_less xs).trans hnum

theorem compare_timeout (xs : List (Bool × Bool)) (fuel : ℕ) (hf : fuel < xs.length) :
    tapeDecision compareMachine compareAccept (xs.map some) fuel = none := by
  cases hr : tapeDecision compareMachine compareAccept (xs.map some) fuel with
  | none => rfl
  | some b =>
      exfalso
      obtain ⟨s, cfg, hs, hafter, hhalt, _⟩ :=
        (clocked_tape_decision_halt_and_timeout _ _ compareMachine compareAccept _ fuel b).mp hr
      have hsl : s < xs.length := lt_of_le_of_lt hs hf
      rw [compare_after xs s hsl.le] at hafter
      cases Option.some.inj hafter
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[s]
          (Turing.Tape.mk₁ (xs.map some))).head = some xs[s] := by
        rw [pairedTape_head, List.getI_eq_getElem _ (by simpa using! hsl)]
        simp [List.getElem_map]
      have ht := (TM0_step_eq_none compareMachine _).mp hhalt
      change compareMachine _ ((Turing.Tape.move Turing.Dir.right)^[s]
        (Turing.Tape.mk₁ (xs.map some))).head = none at ht
      rw [hhead] at ht
      simp [compareMachine] at ht

theorem compareRegisters_correct {n : ℕ} (x y : Reg n) :
    compareRegisters x y = some (decide (binaryValue (List.ofFn x) < binaryValue (List.ofFn y))) := by
  simpa [compareRegisters, registerPairs, List.map_ofFn] using! compare_correct (registerPairs x y)

theorem tableCompare_correct {N width : ℕ} (T : EncodedTable N width) (i j : Fin N) :
    tableCompare T i j = some (decide (tableValue T i < tableValue T j)) :=
  compareRegisters_correct _ _

theorem tableCompare_marked_card {N width : ℕ} (T : EncodedTable N width) (y : Fin N) :
    let R := Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable.ofTable (tableValue T)
    (Finset.univ.filter (fun j => tableCompare T j (R.indexOfRank y) = some true)).card =
      (R.lowerCut y).val := by
  intro R
  have hp : ∀ j, tableCompare T j (R.indexOfRank y) = some true ↔
      R.value j < R.value (R.indexOfRank y) := by
    intro j
    change tableCompare T j (R.indexOfRank y) = some true ↔
      tableValue T j < tableValue T (R.indexOfRank y)
    simp [tableCompare_correct]
  calc
    _ = (Finset.univ.filter (fun j => R.value j < R.value (R.indexOfRank y))).card :=
      congrArg Finset.card (Finset.filter_congr fun j _ => hp j)
    _ = _ := R.marked_card y

theorem initialIndexWeights_total (N : ℕ) : weightTotal (fun _ : Fin N => 1) = N := by
  simp [weightTotal]

theorem initialIndex_rank_law {N width : ℕ} (T : EncodedTable N width) (hN : 0 < N)
    (cap : ℕ) (r : Fin N) :
    let R := Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable.ofTable (tableValue T)
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (initialIndexCode N cap).law
      (fun z => rejectionOutcome z.1.1 = .inl (R.indexOfRank r)) =
      1 / (N : ℝ≥0∞) * (1 - coinRejectMass (Nat.clog 2 N) N ^ cap) := by
  intro R
  have hW : 0 < weightTotal (fun _ : Fin N => 1) := by rw [initialIndexWeights_total]; exact hN
  have hb : weightTotal (fun _ : Fin N => 1) ≤ 2 ^ Nat.clog 2 N := by
    rw [initialIndexWeights_total]
    exact Nat.le_pow_clog (by decide : 1 < 2) N
  simpa only [initialIndexCode, initialIndexWeights_total, Nat.cast_one, rationalRejectMass] using!
    weightedSampler_return (fun _ : Fin N => 1) (Nat.clog 2 N) cap hW hb (R.indexOfRank r)

theorem initialIndex_never_zero (N : ℕ) (hN : 0 < N) :
    weightedSamplerNever (fun _ : Fin N => 1) (Nat.clog 2 N) = 0 := by
  apply weightedSamplerNever_eq_zero
  · rw [initialIndexWeights_total]; exact hN
  · rw [initialIndexWeights_total]
    exact Nat.le_pow_clog (by decide : 1 < 2) N
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount Matrix

theorem encodeGate_unitary {N : ℕ} {U : Matrix (Fin N × Bool) (Fin N × Bool) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N × Bool) ℂ) :
    encodeGate U ∈ Matrix.unitaryGroup (Fin (N * 2)) ℂ := unitaryGroup_reindex _ hU

theorem encodeGate_apply {N : ℕ} (U : Matrix (Fin N × Bool) (Fin N × Bool) ℂ)
    (ψ : QState (Fin N × Bool)) :
    ApplyGate (encodeGate U) (encodeState ψ) = encodeState (ApplyGate U ψ) := by
  ext x
  exact (indexBitEquiv N).symm.sum_comp
    (fun y => U ((indexBitEquiv N).symm x) y * ψ y)

theorem encodeCircuit_run {N : ℕ} (O : Matrix (Fin N × Bool) (Fin N × Bool) ℂ)
    (C : Circuit (Fin N × Bool)) (ψ : QState (Fin N × Bool)) :
    Run (encodeGate O) (encodeCircuit C) (encodeState ψ) = encodeState (Run O C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          change Run (encodeGate O) (.gate (encodeGate U) :: encodeCircuit C) (encodeState ψ) = _
          simp only [Run, encodeGate_apply, ih]
      | query =>
          change Run (encodeGate O) (.query :: encodeCircuit C) (encodeState ψ) = _
          simp only [Run, encodeGate_apply, ih]

theorem resetFlip_involutive (N : ℕ) (b : Bool) : Function.Involutive (resetFlip N b) := by
  intro x
  have hx (a b : Bool) : ((a ^^ b) ^^ b) = a := by cases a <;> cases b <;> rfl
  simp only [resetFlip, Equiv.symm_apply_apply, hx]
  exact (indexBitEquiv N).apply_symm_apply x

theorem checkedReadout_legal (N : ℕ) : observedWellFormed (checkedReadout N) := by
  intro x
  exact ⟨permMatrix_unitary (resetFlip_involutive N _), fun _ => trivial⟩

theorem collapse_singleton {D : ℕ} (ψ : QState (Fin D)) (x : Fin D) :
    Collapse ψ (Finset.univ.filter fun y => y = x) = ψ x • Qatlib.Foundations.PureStateMath.Ket x := by
  ext y
  by_cases h : y = x
  · subst y; simp [collapse_apply, Qatlib.Foundations.PureStateMath.Ket]
  · simp [collapse_apply, Qatlib.Foundations.PureStateMath.Ket, h]

theorem reset_collapsed {N : ℕ} (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) :
    ApplyGate (resetGate N ((indexBitEquiv N).symm x).2)
      (Collapse ψ (Finset.univ.filter fun y => y = x)) =
      ψ x • Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, false)) := by
  rw [collapse_singleton]
  rw [ApplyGate, Matrix.mulVec_smul]
  rw [show (resetGate N ((indexBitEquiv N).symm x).2) *ᵥ Qatlib.Foundations.PureStateMath.Ket x =
    Qatlib.Foundations.PureStateMath.Ket (resetFlip N ((indexBitEquiv N).symm x).2 x) from
      applyGate_permMatrix_ket (resetFlip_involutive N _) x]
  simp [resetFlip]

theorem encodeState_ket {N : ℕ} (p : Fin N × Bool) :
    encodeState (Qatlib.Foundations.PureStateMath.Ket p) = Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N p) := by
  ext x
  simp [encodeState, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]

theorem encoded_query_ket {N : ℕ} (f : Fin N → Bool) (i : Fin N) (b : Bool) :
    ApplyGate (encodeGate (BitOracleOn f)) (Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (i,b))) =
      Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (i, b ^^ f i)) := by
  rw [← encodeState_ket, encodeGate_apply, applyGate_bitOracleOn_ket, encodeState_ket]

theorem query_reset_collapsed {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) :
    ApplyGate (encodeGate (BitOracleOn f))
      (ApplyGate (resetGate N ((indexBitEquiv N).symm x).2)
        (Collapse ψ (Finset.univ.filter fun y => y = x))) =
      ψ x • Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, f ((indexBitEquiv N).symm x).1)) := by
  rw [reset_collapsed, ApplyGate, Matrix.mulVec_smul]
  rw [show encodeGate (BitOracleOn f) *ᵥ Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, false)) =
    Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, f ((indexBitEquiv N).symm x).1)) from
      by simpa only [Bool.false_xor] using! encoded_query_ket f _ false]

theorem collapse_encoded_bit {N : ℕ} (c : ℂ) (p : Fin N × Bool) (b : Fin 2) :
    Collapse (c • Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N p)) (Finset.univ.filter fun y => bitLabel N y = b) =
      if boolEquivFin2 p.2 = b then c • Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N p) else 0 := by
  ext y
  by_cases hy : y = indexBitEquiv N p
  · subst y
    by_cases hb : boolEquivFin2 p.2 = b <;> simp [collapse_apply, bitLabel, Qatlib.Foundations.PureStateMath.Ket, hb]
  · by_cases hb : boolEquivFin2 p.2 = b <;> simp [collapse_apply, Qatlib.Foundations.PureStateMath.Ket, hy, hb]

theorem checkedReadout_traces {N : ℕ} (f : Fin N → Bool) (ψ : QState (Fin (N * 2))) :
    observedTraces (encodeGate (BitOracleOn f)) (checkedReadout N) ψ =
      (List.ofFn (fun x : Fin (N * 2) => List.ofFn (fun b : Fin 2 => checkedTrace f ψ x b))).flatten := by
  unfold checkedReadout
  simp only [observedTraces]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext x
  simp only [List.map_ofFn, List.map_flatten, Function.comp_def, List.map_singleton,
    id_eq, query_reset_collapsed, collapse_encoded_bit]
  change (List.ofFn (fun b : Fin 2 => [checkedTrace f ψ x b])).flatten = _
  simp [List.ofFn_succ]

theorem prependCircuit_traces {D : ℕ} (O : Operator D) (C : Circuit (Fin D))
    (P : ObservedCircuit (Fin D)) (ψ : QState (Fin D)) :
    observedTraces O (prependCircuit C P) ψ =
      (observedTraces O P (Run O C ψ)).map (addCircuitCounts C) := by
  induction C generalizing ψ with
  | nil =>
      have h : addCircuitCounts ([] : Circuit (Fin D)) = _root_.id := by
        funext t
        simp only [addCircuitCounts, queryCount_nil, gateCount_nil, Nat.add_zero]
        rfl
      simp only [prependCircuit, Run, h, List.map_id]
  | cons s C ih =>
      cases s <;> simp [prependCircuit, observedTraces, Run, ih, addCircuitCounts,
        QueryCount, GateCount, List.map_map, Function.comp_def, Nat.add_assoc]

theorem prependCircuit_legal {D : ℕ} (C : Circuit (Fin D)) (hC : IsUnitaryCircuit C)
    (P : ObservedCircuit (Fin D)) (hP : observedWellFormed P) :
    observedWellFormed (prependCircuit C P) := by
  induction C with
  | nil => exact hP
  | cons s C ih =>
      cases s with
      | gate U =>
          obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC
          exact ⟨hU, ih hC⟩
      | query => exact ih ((isUnitaryCircuit_query C).mp hC)

theorem encodeCircuit_legal {N : ℕ} (C : Circuit (Fin N × Bool)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (encodeCircuit C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
      cases s with
      | gate U =>
          obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC
          exact (isUnitaryCircuit_gate _ _).mpr ⟨encodeGate_unitary hU, ih hC⟩
      | query => exact (isUnitaryCircuit_query _).mpr (ih ((isUnitaryCircuit_query C).mp hC))

theorem encodeCircuit_counts {N : ℕ} (C : Circuit (Fin N × Bool)) :
    QueryCount (encodeCircuit C) = QueryCount C ∧ GateCount (encodeCircuit C) = GateCount C := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
      cases s <;> simpa [encodeCircuit, encodeStep, QueryCount, GateCount] using! ih

theorem checkedAttempt_legal {N : ℕ} (hN : 0 < N) (j : ℕ) :
    observedWellFormed (checkedAttempt N j) :=
  prependCircuit_legal _ (encodeCircuit_legal _
    (Qatlib.Concepts.SearchStopping.KnownCount.isUnitaryCircuit_groverCircuit (by simpa using! hN) j).lift)
      _ (checkedReadout_legal N)

theorem checkedAttempt_traces {N : ℕ} (A : Finset (Fin N)) (j : ℕ) :
    observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (checkedAttempt N j)
        (encodeState (WithMinus (Uniform (Fin N)))) =
      (List.ofFn (fun x : Fin (N * 2) => List.ofFn (fun b : Fin 2 => attemptTrace A j x b))).flatten := by
  rw [checkedAttempt, prependCircuit_traces, encodeCircuit_run]
  change (observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (checkedReadout N)
    (encodeState (CheckedSearchState A j))).map _ = _
  rw [checkedReadout_traces, List.map_flatten, List.map_ofFn]
  congr 1

theorem checkedTrace_mass {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) (b : Fin 2) :
    branchMass (checkedTrace f ψ x b).state =
      if boolEquivFin2 (f ((indexBitEquiv N).symm x).1) = b then BornProb ψ x else 0 := by
  unfold checkedTrace checkedLeafState
  split_ifs
  · change MeasureProb (ψ x • Qatlib.Foundations.PureStateMath.Ket (indexBitEquiv N
      (((indexBitEquiv N).symm x).1, f ((indexBitEquiv N).symm x).1))) Finset.univ = _
    rw [measureProb_smul, measureProb_univ (normalized_ket _), mul_one]
    rfl
  · simp [branchMass, MeasureProb, BornProb]

theorem attemptTrace_counts {N : ℕ} (A : Finset (Fin N)) (j : ℕ)
    (x : Fin (N * 2)) (b : Fin 2) :
    (attemptTrace A j x b).queries = j + 1 ∧ (attemptTrace A j x b).gates = j + 1 ∧
    (attemptTrace A j x b).measurements = 2 := by
  have hq := (encodeCircuit_counts (LiftCircuit (SearchCircuit (Fin N) j))).1
  have hg := (encodeCircuit_counts (LiftCircuit (SearchCircuit (Fin N) j))).2
  simp only [attemptTrace, addCircuitCounts, checkedTrace, hq, hg, queryCount_liftCircuit,
    gateCount_liftCircuit, Qatlib.Concepts.SearchStopping.KnownCount.queryCount_groverCircuit]
  simp [SearchCircuit, Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit, gateCount_repeatCircuit,
    Qatlib.Concepts.SearchStopping.KnownCount.GroverStep, GateCount, Nat.add_comm]

theorem attemptTrace_output_mass {N : ℕ} (A : Finset (Fin N)) (j : ℕ) (i : Fin N) :
    (∑ a : Bool, branchMass (attemptTrace A j (indexBitEquiv N (i,a)) 1).state) =
      CheckedOutputMass A j i := by
  let f : Fin N → Bool := fun i => decide (i ∈ A)
  have hv : BornProb (VerifyState f i) (i,true) = if i ∈ A then 1 else 0 := by
    rw [VerifyState, run_query_bitOracleOn_ket]
    by_cases hi : i ∈ A <;> simp [f, hi, bornProb_ket]
  change (∑ a : Bool, branchMass (checkedTrace f
    (encodeState (CheckedSearchState A j)) (indexBitEquiv N (i,a)) 1).state) = _
  simp only [checkedTrace_mass, Equiv.symm_apply_apply]
  change _ = (∑ b : Bool,
      BornProb (CheckedSearchState A j) (i,b)) * BornProb (VerifyState f i) (i,true)
  rw [hv]
  by_cases hi : i ∈ A <;> simp [f, hi, boolEquivFin2, BornProb, encodeState]

theorem checkedAttempt_success_sum {N : ℕ} (A : Finset (Fin N)) (j : ℕ) :
    ((observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (checkedAttempt N j)
      (encodeState (WithMinus (Uniform (Fin N))))).map
        (fun t => branchMass t.state * (if t.accepted then (1 : ℝ) else 0))).sum =
      ∑ i : Fin N, CheckedOutputMass A j i := by
  rw [checkedAttempt_traces, List.map_flatten, List.sum_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have ha (x : Fin (N * 2)) (b : Fin 2) : (attemptTrace A j x b).accepted = (b == 1) := rfl
  simp only [Fin.sum_univ_two, ha]
  norm_num
  rw [← (indexBitEquiv N).sum_comp (fun x => branchMass (attemptTrace A j x 1).state),
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => attemptTrace_output_mass A j i)

theorem checkedAttempt_instrument_success {N : ℕ} (hN : 0 < N) (A : Finset (Fin N)) (j : ℕ) :
    (∑ k : Fin (observedLeafCount (checkedAttempt N j)),
      instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary
        (fun i => decide (i ∈ A)))) (checkedAttempt N j) (checkedAttempt_legal hN j))
        (outerProduct (encodeState (WithMinus (Uniform (Fin N))))) k *
      (if (observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (checkedAttempt N j) k).accepted then 1 else 0)) =
      ∑ i : Fin N, CheckedOutputMass A j i := by
  rw [← checkedAttempt_success_sum A j, observedTraces_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  rw [instrumentProb_observedInstrument]
  rfl

theorem bbhtProgram_legal {N : ℕ} (hN : 0 < N) (m : ℕ) : (bbhtProgram N m).Legal := by
  constructor
  · trivial
  · intro i a
    rcases a with ⟨cfg,t⟩
    cases cfg with
    | inr s => trivial
    | inl z => exact checkedAttempt_legal hN z.1.val
noncomputable def bbhtInstrument {N : ℕ} (hN : 0 < N) (m cap : ℕ) (A : Finset (Fin N)) :=
  (bbhtProgram N m).instrument cap (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
    (encodeGate_unitary (bitOracleOn_unitary _)) (bbhtProgram_legal hN m)

theorem bbhtInstrument_success_paths {N : ℕ} (hN : 0 < N) (m cap : ℕ) (A : Finset (Fin N)) :
    (∑ z, instrumentProb (bbhtInstrument hN m cap A) (bbhtInput N) z *
      (if (((bbhtProgram N m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).accepted then 1 else 0)) =
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun j => ∑ i : Fin N, CheckedOutputMass A j.val i) := by
  unfold bbhtInstrument CappedFeedback.instrument
  simp only [Fintype.sum_sigma]
  change (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  unfold codeSuccess
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [FairFeedback.probability_law]
  simp only [FairFeedback.codeWord, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hp : (((bbhtProgram N m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).operator = 1 := rfl
  rw [hp]
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  let go : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ) → ObservedCircuit (Fin (N * 2))
    | .inr _ => .halt false
    | .inl (j,_,_) => checkedAttempt N j.val
  have hgo (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      observedWellFormed (go cfg) := by
    cases cfg with
    | inr s => trivial
    | inl z => exact checkedAttempt_legal hN z.1.val
  change (∑ x : Fin (observedLeafCount (go ((weightedSampler (fun _ : Fin m => 1)
      (Nat.clog 2 m) cap).paths.get c).1.1)),
    instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary _))
      (go _) (hgo _)) (bbhtInput N) x *
      (if (observedLeaf _ (go _) x).accepted then 1 else 0)) = _
  rcases hcfg :
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c).1.1 with s | s
  · rcases s with ⟨j,b,d⟩
    exact checkedAttempt_instrument_success hN A j.val
  · change (∑ j : Fin 1, _) = 0
    rw [Fin.sum_univ_one]
    simp [go, observedLeaf, observedKrausLeaves]
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount Matrix
open Classical

theorem codeSuccess_eq_events {m : ℕ} (p : CoinCode (SamplerRecord m)) (F : Fin m → ℝ) :
    codeSuccess p F = ∑ j : Fin m,
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p.law (fun x => rejectionOutcome x.1.1 = .inl j)).toReal * F j := by
  have hs (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      (match cfg with | .inr _ => 0 | .inl (j,_,_) => F j) =
        ∑ j : Fin m, (if rejectionOutcome cfg = .inl j then (1 : ℝ) else 0) * F j := by
    cases cfg with
    | inr s => simp [rejectionOutcome]
    | inl z => rcases z with ⟨j,b,d⟩; simp [rejectionOutcome]
  unfold codeSuccess
  trans ∑ c : Fin p.paths.length, CoinCode.wordWeight (p.paths.get c).2 *
    ∑ j : Fin m, (if rejectionOutcome (p.paths.get c).1.1 = .inl j then (1 : ℝ) else 0) * F j
  · apply Finset.sum_congr rfl
    intro c _
    exact congrArg (fun y => CoinCode.wordWeight (p.paths.get c).2 * y) (hs _)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [CoinCode.paths_event_toReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> ring

theorem uniformDepth_success {m : ℕ} (hm : 0 < m) (cap : ℕ) (F : Fin m → ℝ) :
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap) F =
      (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
        (∑ j : Fin m, F j) / m := by
  rw [codeSuccess_eq_events]
  have hW : 0 < weightTotal (fun _ : Fin m => 1) := by simpa [weightTotal] using! hm
  have hb : weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m := by
    simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m
  simp_rw [weightedSampler_return _ _ _ hW hb]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]

  have hq : rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap ≤ 1 := by
    rw [← weightedSampler_timeout _ _ _ hb]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
  rw [show weightTotal (fun _ : Fin m => 1) = m from by simp [weightTotal]]
  simp_rw [ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [← Finset.mul_sum]
  ring

theorem bbhtInstrument_success {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (cap : ℕ) (A : Finset (Fin N)) :
    (∑ z, instrumentProb (bbhtInstrument hN m cap A) (bbhtInput N) z *
      (if (((bbhtProgram N m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).accepted then 1 else 0)) =
    (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
      CheckedSuccess A m := by
  rw [bbhtInstrument_success_paths, uniformDepth_success hm]
  unfold CheckedSuccess
  rw [← Fin.sum_univ_eq_sum_range]
  ring
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount Matrix
open Classical
open scoped ComplexOrder

theorem bbhtInput_density {N : ℕ} (hN : 0 < N) : IsDensityOperator (bbhtInput N) := by
  have hψ : Normalized (WithMinus (Uniform (Fin N))) :=
    normalized_tensorState (normalized_uniform (by simpa using! hN)) normalized_minus
  have he : Normalized (encodeState (WithMinus (Uniform (Fin N)))) := by
    change (∑ x : Fin (N * 2), ‖WithMinus (Uniform (Fin N)) ((indexBitEquiv N).symm x)‖ ^ 2) = 1
    exact ((indexBitEquiv N).symm.sum_comp
      (fun p => ‖WithMinus (Uniform (Fin N)) p‖ ^ 2)).trans hψ
  exact ⟨outerProduct_posSemidef _, by rw [bbhtInput, trace_outerProduct, he]; rfl⟩

theorem checkedAttempt_leaf_counts {N : ℕ} (A : Finset (Fin N)) (j : ℕ)
    (k : Fin (observedLeafCount (checkedAttempt N j))) :
    let leaf :=
        observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (checkedAttempt N j) k
    leaf.queries = j + 1 ∧ leaf.gates = j + 1 ∧ leaf.measurements = 2 := by
  let O := encodeGate (BitOracleOn (fun i => decide (i ∈ A)))
  let ψ := encodeState (WithMinus (Uniform (Fin N)))
  have hm : ((observedLeaf O (checkedAttempt N j) k).toTrace ψ) ∈
      observedTraces O (checkedAttempt N j) ψ := by
    rw [observedTraces_eq_ofFn]
    exact List.mem_ofFn.mpr ⟨k,rfl⟩
  rw [show observedTraces O (checkedAttempt N j) ψ = _ from checkedAttempt_traces A j] at hm
  obtain ⟨L,hL,ht⟩ := List.mem_flatten.mp hm
  obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hL
  obtain ⟨b,hb⟩ := List.mem_ofFn.mp ht
  have hq := congrArg BranchTrace.queries hb
  have hg := congrArg BranchTrace.gates hb
  have hm := congrArg BranchTrace.measurements hb
  exact ⟨hq.symm.trans (attemptTrace_counts A j x b).1,
    hg.symm.trans (attemptTrace_counts A j x b).2.1,
    hm.symm.trans (attemptTrace_counts A j x b).2.2⟩

theorem checkedAttempt_instrument_queries {N : ℕ} (hN : 0 < N) (A : Finset (Fin N)) (j : ℕ) :
    (∑ k : Fin (observedLeafCount (checkedAttempt N j)),
      instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary
        (fun i => decide (i ∈ A)))) (checkedAttempt N j) (checkedAttempt_legal hN j))
        (bbhtInput N) k *
      ((observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (checkedAttempt N j) k).queries : ℝ)) = j + 1 := by
  simp_rw [(checkedAttempt_leaf_counts A j _).1]
  rw [← Finset.sum_mul, sum_instrumentProb_isDensityOperator _ (bbhtInput_density hN), one_mul,
    Nat.cast_add, Nat.cast_one]

theorem bbhtInstrument_queries_paths {N : ℕ} (hN : 0 < N) (m cap : ℕ) (A : Finset (Fin N)) :
    (∑ z, instrumentProb (bbhtInstrument hN m cap A) (bbhtInput N) z *
      ((((bbhtProgram N m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).queries : ℝ)) =
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun j => (j.val : ℝ) + 1) := by
  unfold bbhtInstrument CappedFeedback.instrument
  simp only [Fintype.sum_sigma]
  change (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  unfold codeSuccess
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [FairFeedback.probability_law]
  simp only [FairFeedback.codeWord, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hp : (((bbhtProgram N m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).operator = 1 := rfl
  rw [hp]
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  let go : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ) → ObservedCircuit (Fin (N * 2))
    | .inr _ => .halt false
    | .inl (j,_,_) => checkedAttempt N j.val
  have hgo (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      observedWellFormed (go cfg) := by
    cases cfg with
    | inr s => trivial
    | inl z => exact checkedAttempt_legal hN z.1.val
  have hqp : (((bbhtProgram N m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).queries = 0 := rfl
  simp only [FairFeedback.record, hqp, Nat.zero_add]
  change (∑ x : Fin (observedLeafCount (go ((weightedSampler (fun _ : Fin m => 1)
      (Nat.clog 2 m) cap).paths.get c).1.1)),
    instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary _))
      (go _) (hgo _)) (bbhtInput N) x *
      ((observedLeaf _ (go _) x).queries : ℝ)) = _
  rcases hcfg :
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c).1.1 with s | s
  · rcases s with ⟨j,b,d⟩
    exact checkedAttempt_instrument_queries hN A j.val
  · change (∑ j : Fin 1, _) = 0
    rw [Fin.sum_univ_one]
    simp [go, observedLeaf, observedKrausLeaves]

theorem bbhtInstrument_expected_queries {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (cap : ℕ) (A : Finset (Fin N)) :
    (∑ z, instrumentProb (bbhtInstrument hN m cap A) (bbhtInput N) z *
      ((((bbhtProgram N m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).queries : ℝ)) =
    (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
      ((m : ℝ) + 1) / 2 := by
  rw [bbhtInstrument_queries_paths, uniformDepth_success hm,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => (j : ℝ) + 1) m]
  have hs (k : ℕ) : (∑ j ∈ Finset.range k, ((j : ℝ) + 1)) = (k : ℝ) * (k + 1) / 2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]; ring
  rw [hs]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem bbhtProgram_capacity (N m : ℕ) :
    ∀ i, weightTotal ((bbhtProgram N m).weights i) ≤ 2 ^ (bbhtProgram N m).width i := by
  intro i
  change weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m
  simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m

theorem bbhtProgram_weights_positive (N : ℕ) {m : ℕ} (hm : 0 < m) :
    ∀ i, 0 < weightTotal ((bbhtProgram N m).weights i) := by
  intro i
  change 0 < weightTotal (fun _ : Fin m => 1)
  simpa [weightTotal] using! hm

theorem bbhtProgram_timeout {N : ℕ} (hN : 0 < N) (m cap : ℕ) (A : Finset (Fin N)) :
    (bbhtProgram N m).timeoutMass cap (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
      (encodeGate_unitary (bitOracleOn_unitary _)) (bbhtProgram_legal hN m) (bbhtInput N) =
      rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap := by
  unfold CappedFeedback.timeoutMass
  rw [CappedFeedback.timeout _ _ _ _ _ _ (bbhtProgram_capacity N m)]
  change ENNReal.ofReal (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  have hp : instrumentProb
    (observedInstrument (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
      (encodeGate_unitary (bitOracleOn_unitary _)) (.halt true) trivial)
        (bbhtInput N) (0 : Fin 1) = 1 := by
    rw [instrumentProb, observedInstrument, Instrument.ofKraus_branch]
    change (Matrix.trace (conjBranch (1 : Operator (N * 2)) (bbhtInput N))).re = 1
    simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
      (bbhtInput_density hN).2, Complex.one_re]
  change ENNReal.ofReal (instrumentProb
    (observedInstrument (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
      (encodeGate_unitary (bitOracleOn_unitary _)) (.halt true) trivial)
        (bbhtInput N) (0 : Fin 1) *
      (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) = _
  rw [hp, one_mul]
  apply ENNReal.ofReal_toReal
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
    have hb := bbhtProgram_capacity N m (0 : Fin 1)
    change weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m at hb
    rw [← weightedSampler_timeout _ _ _ hb]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _)

theorem bbhtProgram_never_zero {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (A : Finset (Fin N)) :
    (bbhtProgram N m).neverMass (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
      (encodeGate_unitary (bitOracleOn_unitary _)) (bbhtProgram_legal hN m) (bbhtInput N) = 0 :=
  (bbhtProgram N m).neverMass_eq_zero _ _ _ _ (bbhtProgram_weights_positive N hm) (bbhtProgram_capacity N m)

theorem mem_nativeMarked {N width : ℕ} (T : EncodedTable N width) (y i : Fin N) :
    i ∈ nativeMarked T y ↔ tableValue T i < tableValue T y := by
  simp [nativeMarked, tableCompare_correct]

theorem attemptTrace_native_output_mass {N width : ℕ} (hN : 0 < N)
    (T : EncodedTable N width) (y : Fin N) (j : ℕ) (i : Fin N) :
    (∑ a : Bool, branchMass (attemptTrace (nativeMarked T y) j (indexBitEquiv N (i,a)) 1).state) =
      if tableValue T i < tableValue T y then BornProb (SearchState (nativeMarked T y) j) i else 0 := by
  rw [attemptTrace_output_mass,
      (search_checked_attempt (by simpa using! hN) (nativeMarked T y) j).2.1 i]
  simp only [mem_nativeMarked]

theorem hadamardWord_length (n : ℕ) : (hadamardWord n).length = n := by simp [hadamardWord]

theorem hadamardWord_legal (n : ℕ) : finiteWordLegal n (hadamardWord n) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact decide_eq_true i.isLt

theorem finiteCode_h_eq_local {n : ℕ} (i : Fin n) :
    finiteCodeMatrix n (.h i.val) = localGateMatrix (.h i) := by
  rw [finiteCodeMatrix, dif_pos i.isLt]
  ext x y
  rw [wireGate_apply, localGateMatrix_h]

theorem hadamardWord_circuit (n : ℕ) :
    finiteCodeCircuit n (hadamardWord n) = localProgramCircuit (localHadamard n) := by
  unfold finiteCodeCircuit hadamardWord localProgramCircuit localHadamard
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  rw [finiteCode_h_eq_local]

theorem hadamardWord_run (n : ℕ) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (hadamardWord n)) ψ =
      ApplyGate (HadamardN n) ψ := by
  rw [hadamardWord_circuit, (localDyadicProgram_run_adjoint_cost n (localHadamard n) ψ).1,
    localProgramMatrix_localHadamard]

theorem hadamardWord_prepare (n : ℕ) :
    finiteWordRun n (hadamardWord n) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)) = some (Uniform (Reg n)) := by
  rw [finiteWordRun, hadamardWord_legal]
  simp only [↓reduceIte, hadamardWord_run, applyGate_hadamardN_ket_zero]

theorem uniformMinusWord_length (n : ℕ) : (uniformMinusWord n).length = n + 2 := by
  simp only [uniformMinusWord, List.length_cons, hadamardWord_length]

theorem uniformMinusWord_legal (n : ℕ) : finiteWordLegal (n + 1) (uniformMinusWord n) = true := by
  simp only [uniformMinusWord, finiteWordLegal, List.all_cons, finiteCodeLegal,
    decide_eq_true (Nat.lt_succ_self n), Bool.true_and]
  exact hadamardWord_legal (n + 1)

theorem uniformMinusWord_x (n : ℕ) :
    ApplyGate (finiteCodeMatrix (n + 1) (.x n)) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr (n + 1))) = Qatlib.Foundations.PureStateMath.Ket (lastOne n) := by
  rw [finiteCodeMatrix, dif_pos (Nat.lt_succ_self n), applyGate_wireGate_ket]
  simp [ZeroStr, PauliX, permMatrix, lastOne]
  rfl

theorem uniformMinusWord_run (n : ℕ) :
    Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (uniformMinusWord n)) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr (n + 1))) =
        relabelState (regSuccEquiv n).symm (TensorState (Uniform (Reg n)) Minus) := by
  change Run _ (.gate _ :: finiteCodeCircuit (n + 1) (hadamardWord (n + 1))) _ = _
  rw [Run, uniformMinusWord_x, hadamardWord_run]
  ext x
  change (HadamardN (n + 1) *ᵥ Qatlib.Foundations.PureStateMath.Ket (lastOne n)) x = _
  rw [mulVec_ket_apply]
  simp only [HadamardN, Matrix.of_apply, Fin.prod_univ_castSucc, lastOne,
    Function.update_self]
  have hbit (i : Fin n) : (Function.update (ZeroStr (n + 1)) (Fin.last n) true) i.castSucc = false := by
    rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
    rfl
  simp only [hbit]
  have hp : (∏ i : Fin n, Hadamard (x i.castSucc) false) =
      Uniform (Reg n) (fun i => x i.castSucc) := by
    have h := congrFun (applyGate_hadamardN_ket_zero n) (fun i => x i.castSucc)
    simpa only [ApplyGate, mulVec_ket_apply, HadamardN, Matrix.of_apply, ZeroStr] using! h
  rw [hp]
  rfl

theorem prepPowCircuit_counts (n : ℕ) :
    QueryCount (prepPowCircuit n) = 0 ∧ GateCount (prepPowCircuit n) = n + 2 := by
  have h := relabelCircuit_legality_resources (prepLayout n)
    (finiteCodeCircuit (n + 1) (uniformMinusWord n))
  exact ⟨h.2.1.trans (finiteCodeCircuit_counts _ _).1,
    h.2.2.1.trans ((finiteCodeCircuit_counts _ _).2.trans (uniformMinusWord_length n))⟩

theorem prepPowCircuit_legal (n : ℕ) : IsUnitaryCircuit (prepPowCircuit n) :=
  (relabelCircuit_legality_resources _ _).1.mpr
    ((finite_gate_description_rejection_unitarity_and_counts _ _).2 (uniformMinusWord_legal n)).1

theorem relabel_ket {I J : Type} [DecidableEq I] [DecidableEq J] (e : I ≃ J) (i : I) :
    relabelState e (Qatlib.Foundations.PureStateMath.Ket i) = Qatlib.Foundations.PureStateMath.Ket (e i) := by
  ext j
  simp [relabelState, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]

theorem prepLayout_state (n : ℕ) :
    relabelState (prepLayout n)
      (relabelState (regSuccEquiv n).symm (TensorState (Uniform (Reg n)) Minus)) =
      encodeState (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.WithMinus (Uniform (Fin (2 ^ n)))) := by
  ext x
  simp [prepLayout, relabelState, encodeState, Qatlib.Concepts.QueryComplexity.AdaptiveQuery.WithMinus,
    TensorState, Uniform]

theorem prepPowCircuit_run (n : ℕ) (O : Operator (2 ^ n * 2)) :
    Run O (prepPowCircuit n) (Qatlib.Foundations.PureStateMath.Ket (prepLayout n (ZeroStr (n + 1)))) =
      encodeState (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.WithMinus (Uniform (Fin (2 ^ n)))) := by
  have h := (run_relabelCircuit_readout (prepLayout n)
    (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (uniformMinusWord n)) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr (n + 1))) ∅).1
  rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one, relabel_ket,
      uniformMinusWord_run, prepLayout_state] at h
  exact (run_eq_of_queryCount_eq_zero O 1 _ (prepPowCircuit_counts n).1 _).trans h

theorem preparedAttempt_legal (n j : ℕ) : observedWellFormed (preparedAttempt n j) :=
  prependCircuit_legal _ (prepPowCircuit_legal n) _
    (checkedAttempt_legal (Nat.two_pow_pos n) j)

theorem preparedAttempt_traces (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (preparedAttempt n j)
      (Qatlib.Foundations.PureStateMath.Ket (prepZero n)) =
      (observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (checkedAttempt (2 ^ n) j)
        (encodeState (WithMinus (Uniform (Fin (2 ^ n)))))).map (addCircuitCounts (prepPowCircuit n)) := by
  rw [preparedAttempt, prependCircuit_traces, prepZero, prepPowCircuit_run]

theorem preparedAttempt_success_sum (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    ((observedTraces (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (preparedAttempt n j)
      (Qatlib.Foundations.PureStateMath.Ket (prepZero n))).map
        (fun t => branchMass t.state * (if t.accepted then (1 : ℝ) else 0))).sum =
      ∑ i : Fin (2 ^ n), CheckedOutputMass A j i := by
  rw [preparedAttempt_traces, List.map_map]
  exact checkedAttempt_success_sum A j

theorem preparedAttempt_instrument_success (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ k : Fin (observedLeafCount (preparedAttempt n j)),
      instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary
        (fun i => decide (i ∈ A)))) (preparedAttempt n j) (preparedAttempt_legal n j))
        (preparedInput n) k *
      (if (observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (preparedAttempt n j) k).accepted then 1 else 0)) =
      ∑ i : Fin (2 ^ n), CheckedOutputMass A j i := by
  rw [← preparedAttempt_success_sum n j A, observedTraces_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  rw [preparedInput, instrumentProb_observedInstrument]
  rfl

theorem preparedBBHTProgram_legal (n m : ℕ) : (preparedBBHTProgram n m).Legal := by
  constructor
  · trivial
  · intro i a
    rcases a with ⟨cfg,t⟩
    cases cfg with
    | inr s => trivial
    | inl z => exact preparedAttempt_legal n z.1.val
noncomputable def preparedBBHTInstrument (n m cap : ℕ) (A : Finset (Fin (2 ^ n))) :=
  (preparedBBHTProgram n m).instrument cap (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
    (encodeGate_unitary (bitOracleOn_unitary _)) (preparedBBHTProgram_legal n m)

theorem preparedBBHTInstrument_success_paths (n m cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      (if (((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).accepted then 1 else 0)) =
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun j => ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) := by
  unfold preparedBBHTInstrument CappedFeedback.instrument
  simp only [Fintype.sum_sigma]
  change (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  unfold codeSuccess
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [FairFeedback.probability_law]
  simp only [FairFeedback.codeWord, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hp : (((preparedBBHTProgram n m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).operator = 1 := rfl
  rw [hp]
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  let go : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ) → ObservedCircuit (Fin (2 ^ n * 2))
    | .inr _ => .halt false
    | .inl (j,_,_) => preparedAttempt n j.val
  have hgo (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      observedWellFormed (go cfg) := by
    cases cfg with
    | inr s => trivial
    | inl z => exact preparedAttempt_legal n z.1.val
  change (∑ x : Fin (observedLeafCount (go ((weightedSampler (fun _ : Fin m => 1)
      (Nat.clog 2 m) cap).paths.get c).1.1)),
    instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary _))
      (go _) (hgo _)) (preparedInput n) x *
      (if (observedLeaf _ (go _) x).accepted then 1 else 0)) = _
  rcases hcfg :
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c).1.1 with s | s
  · rcases s with ⟨j,b,d⟩
    exact preparedAttempt_instrument_success n j.val A
  · change (∑ j : Fin 1, _) = 0
    rw [Fin.sum_univ_one]
    simp [go, observedLeaf, observedKrausLeaves]

theorem preparedBBHTInstrument_success (n : ℕ) {m : ℕ} (hm : 0 < m)
    (cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      (if (((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).accepted then 1 else 0)) =
    (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
      CheckedSuccess A m := by
  rw [preparedBBHTInstrument_success_paths, uniformDepth_success hm]
  unfold CheckedSuccess
  rw [← Fin.sum_univ_eq_sum_range]
  ring

theorem preparedInput_density (n : ℕ) : IsDensityOperator (preparedInput n) := by
  exact ⟨outerProduct_posSemidef _, by
    rw [preparedInput, trace_outerProduct, normalized_ket]; rfl⟩

theorem preparedAttempt_leaf_counts (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (k : Fin (observedLeafCount (preparedAttempt n j))) :
    let leaf :=
        observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (preparedAttempt n j) k
    leaf.queries = j + 1 ∧ leaf.gates = j + 1 + (n + 2) ∧ leaf.measurements = 2 := by
  let O := encodeGate (BitOracleOn (fun i => decide (i ∈ A)))
  let ψ := Qatlib.Foundations.PureStateMath.Ket (prepZero n)
  have hm : ((observedLeaf O (preparedAttempt n j) k).toTrace ψ) ∈
      observedTraces O (preparedAttempt n j) ψ := by
    rw [observedTraces_eq_ofFn]
    exact List.mem_ofFn.mpr ⟨k,rfl⟩
  rw [show observedTraces O (preparedAttempt n j) ψ = _ from preparedAttempt_traces n j A] at hm
  obtain ⟨t,ht,he⟩ := List.mem_map.mp hm
  rw [checkedAttempt_traces] at ht
  obtain ⟨L,hL,ht⟩ := List.mem_flatten.mp ht
  obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hL
  obtain ⟨b,hb⟩ := List.mem_ofFn.mp ht
  subst t
  have hq := congrArg BranchTrace.queries he
  have hg := congrArg BranchTrace.gates he
  have hm := congrArg BranchTrace.measurements he
  have hc := attemptTrace_counts A j x b
  simp only [addCircuitCounts, (prepPowCircuit_counts n).1, (prepPowCircuit_counts n).2,
    Nat.add_zero, hc.1, hc.2.1, hc.2.2] at hq hg hm
  exact ⟨hq.symm, hg.symm, hm.symm⟩

theorem preparedAttempt_instrument_queries (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ k : Fin (observedLeafCount (preparedAttempt n j)),
      instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary
        (fun i => decide (i ∈ A)))) (preparedAttempt n j) (preparedAttempt_legal n j))
        (preparedInput n) k *
      ((observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (preparedAttempt n j) k).queries : ℝ)) = j + 1 := by
  simp_rw [(preparedAttempt_leaf_counts n j A _).1]
  rw [← Finset.sum_mul, sum_instrumentProb_isDensityOperator _ (preparedInput_density n), one_mul,
    Nat.cast_add, Nat.cast_one]

theorem preparedAttempt_instrument_gates (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ k : Fin (observedLeafCount (preparedAttempt n j)),
      instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary
        (fun i => decide (i ∈ A)))) (preparedAttempt n j) (preparedAttempt_legal n j))
        (preparedInput n) k *
      ((observedLeaf (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (preparedAttempt n j) k).gates : ℝ)) = (j : ℝ) + 1 + (n + 2) := by
  simp_rw [(preparedAttempt_leaf_counts n j A _).2.1]
  rw [← Finset.sum_mul, sum_instrumentProb_isDensityOperator _ (preparedInput_density n), one_mul]
  push_cast
  rfl

theorem preparedBBHTInstrument_queries_paths (n m cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      ((((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).queries : ℝ)) =
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun j => (j.val : ℝ) + 1) := by
  unfold preparedBBHTInstrument CappedFeedback.instrument
  simp only [Fintype.sum_sigma]
  change (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  unfold codeSuccess
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [FairFeedback.probability_law]
  simp only [FairFeedback.codeWord, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hp : (((preparedBBHTProgram n m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).operator = 1 := rfl
  rw [hp]
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  let go : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ) → ObservedCircuit (Fin (2 ^ n * 2))
    | .inr _ => .halt false
    | .inl (j,_,_) => preparedAttempt n j.val
  have hgo (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      observedWellFormed (go cfg) := by
    cases cfg with
    | inr s => trivial
    | inl z => exact preparedAttempt_legal n z.1.val
  have hqp : (((preparedBBHTProgram n m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).queries = 0 := rfl
  simp only [FairFeedback.record, hqp, Nat.zero_add]
  change (∑ x : Fin (observedLeafCount (go ((weightedSampler (fun _ : Fin m => 1)
      (Nat.clog 2 m) cap).paths.get c).1.1)),
    instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary _))
      (go _) (hgo _)) (preparedInput n) x *
      ((observedLeaf _ (go _) x).queries : ℝ)) = _
  rcases hcfg :
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c).1.1 with s | s
  · rcases s with ⟨j,b,d⟩
    exact preparedAttempt_instrument_queries n j.val A
  · change (∑ j : Fin 1, _) = 0
    rw [Fin.sum_univ_one]
    simp [go, observedLeaf, observedKrausLeaves]

theorem preparedBBHTInstrument_gates_paths (n m cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      ((((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).gates : ℝ)) =
    codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun j => (j.val : ℝ) + 1 + (n + 2)) := by
  unfold preparedBBHTInstrument CappedFeedback.instrument
  simp only [Fintype.sum_sigma]
  change (∑ i : Fin 1, _) = _
  rw [Fin.sum_univ_one]
  unfold codeSuccess
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [FairFeedback.probability_law]
  simp only [FairFeedback.codeWord, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hp : (((preparedBBHTProgram n m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).operator = 1 := rfl
  rw [hp]
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  let go : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ) → ObservedCircuit (Fin (2 ^ n * 2))
    | .inr _ => .halt false
    | .inl (j,_,_) => preparedAttempt n j.val
  have hgo (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin m × ℕ × ℕ)) :
      observedWellFormed (go cfg) := by
    cases cfg with
    | inr s => trivial
    | inl z => exact preparedAttempt_legal n z.1.val
  have hqp : (((preparedBBHTProgram n m).compile cap).prefixLeaf
      (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) (0 : Fin 1)).gates = 0 := rfl
  simp only [FairFeedback.record, hqp, Nat.zero_add]
  change (∑ x : Fin (observedLeafCount (go ((weightedSampler (fun _ : Fin m => 1)
      (Nat.clog 2 m) cap).paths.get c).1.1)),
    instrumentProb (observedInstrument _ (encodeGate_unitary (bitOracleOn_unitary _))
      (go _) (hgo _)) (preparedInput n) x *
      ((observedLeaf _ (go _) x).gates : ℝ)) = _
  rcases hcfg :
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c).1.1 with s | s
  · rcases s with ⟨j,b,d⟩
    exact preparedAttempt_instrument_gates n j.val A
  · change (∑ j : Fin 1, _) = 0
    rw [Fin.sum_univ_one]
    simp [go, observedLeaf, observedKrausLeaves]

theorem preparedBBHTInstrument_expected_queries (n : ℕ) {m : ℕ} (hm : 0 < m)
    (cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      ((((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).queries : ℝ)) =
    (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
      ((m : ℝ) + 1) / 2 := by
  rw [preparedBBHTInstrument_queries_paths]
  have h := bbhtInstrument_expected_queries (Nat.two_pow_pos n) hm cap A
  rwa [bbhtInstrument_queries_paths] at h
end Qatlib.Concepts.AmplitudeSearch.Amplification
