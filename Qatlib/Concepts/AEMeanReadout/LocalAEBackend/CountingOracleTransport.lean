/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology

private theorem sum_filterMap_id_eq_map_getD (l : List (Option ℕ)) :
    (l.filterMap id).sum = (l.map (fun o : Option ℕ => Option.getD o 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | none =>
      change (l.filterMap id).sum = (0 : ℕ) + (l.map (fun o : Option ℕ => Option.getD o 0)).sum
      rw [ih, Nat.zero_add]
    | some b =>
      change (b : ℕ) + (l.filterMap id).sum
        = (b : ℕ) + (l.map (fun o : Option ℕ => Option.getD o 0)).sum
      rw [ih]

theorem recordGrids_sum {n : ℕ} (grid : Fin n → ℕ) (exec : Fin n → Bool) (m : ℕ) :
    (recordGrids grid exec m).sum
      = (∑ l : Fin n, if exec l then grid l else 0) + m := by
  unfold recordGrids
  rw [List.sum_append, List.sum_singleton, sum_filterMap_id_eq_map_getD, List.map_ofFn]
  rw [List.sum_ofFn]
  apply congrArg (fun x => x + m)
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : exec i = true
  · simp [h]
  · simp [h]

def basicApproxCountLoopGrid (l : ℕ) : ℕ := 2 * 2 ^ l

noncomputable def basicApproxCountExecFlag (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (l : Fin (basicApproxCountLoopCap N)) : Bool :=
  decide (l.val < basicApproxCountStop N ω)

noncomputable def basicApproxCountExecutedGrids (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : List ℕ :=
  recordGrids (fun l : Fin (basicApproxCountLoopCap N) => basicApproxCountLoopGrid l.val)
    (basicApproxCountExecFlag N ω)
    (basicApproxCountFinalM ε (basicApproxCountStop N ω))

theorem basicApproxCount_sourceLedger_eq (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) :
    basicApproxCountTotalCost N ε ω
      = (recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
        (basicApproxCountExecFlag N ω)
        (basicApproxCountFinalM ε (basicApproxCountStop N ω))).sum := by
  have hsum : (∑ l : Fin (basicApproxCountLoopCap N),
        if basicApproxCountExecFlag N ω l then 2 * 2 ^ l.val else 0)
      = ∑ l : Fin (basicApproxCountLoopCap N),
        if l.val < basicApproxCountStop N ω then 2 * 2 ^ l.val else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : l.val < basicApproxCountStop N ω
    · simp [basicApproxCountExecFlag, h]
    · simp [basicApproxCountExecFlag, h]
  rw [basicApproxCountTotalCost, recordGrids_sum, hsum]

theorem basicApproxCount_executedGrids_eq (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) :
    basicApproxCountExecutedGrids N ε ω
      = recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
        (basicApproxCountExecFlag N ω)
        (basicApproxCountFinalM ε (basicApproxCountStop N ω)) := rfl

theorem basicApproxCount_final_grid_pos (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) :
    1 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω) := by
  have hinner : 0 < 20 * Real.pi ^ 2 / ε * (2 ^ basicApproxCountStop N ω : ℝ) := by
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have h2 : (0 : ℝ) < (2 ^ basicApproxCountStop N ω : ℝ) := by positivity
    positivity
  have hceil : 0 < basicApproxCountFinalM ε (basicApproxCountStop N ω) := by
    rw [basicApproxCountFinalM]
    exact (Nat.ceil_pos).2 hinner
  omega

theorem basicApproxCount_oracle_cost_transport (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N)
    (ε : ℝ) (hε : 0 < ε) :
    JointRecordOracleCostTransport
      (basicApproxCountPrefixWeight hN S)
      (fun ω => recordGrids
        (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
        (basicApproxCountExecFlag N ω)
        (basicApproxCountFinalM ε (basicApproxCountStop N ω)))
      (fun ω => basicApproxCountTotalCost N ε ω) := by
  refine clause89_basic_of_pos (basicApproxCountLoopCap N) _ (basicApproxCountPrefixWeight hN S)
    (basicApproxCountExecFlag N)
    (fun ω => basicApproxCountFinalM ε (basicApproxCountStop N ω))
    (fun ω => basicApproxCountTotalCost N ε ω) ?_ ?_
  · intro ω
    exact basicApproxCount_final_grid_pos N ε hε ω
  · intro ω
    exact basicApproxCount_sourceLedger_eq N ε ω

noncomputable def exactCountExecutedGrids (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) : List ℕ :=
  recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
    (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
      ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))

theorem exactCount_sourceLedger_eq (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) :
    2 * exactCountM₀ N + exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)
      = (recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
        (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))).sum := by
  rw [recordGrids_sum]
  simp

theorem exactCount_executedGrids_eq (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) :
    exactCountExecutedGrids N z
      = recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
        (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) := rfl

noncomputable def exactCountPathWeight {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM0 : 2 ≤ exactCountM₀ N)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) : ℝ :=
  ((aeLaw (exactCountM₀ N) (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM0).prob z.1) *
  ((aeLaw (exactCountM₀ N) (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM0).prob z.2)

theorem exactCount_oracle_cost_transport (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N)
    (hM0 : 2 ≤ exactCountM₀ N)
    (hM : ∀ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) :
    JointRecordOracleCostTransport (exactCountPathWeight hN S hM0)
      (exactCountExecutedGrids N)
      (fun z => 2 * exactCountM₀ N + exactCountGrid N
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) := by
  refine clause89_exact_of_pos (exactCountM₀ N) _ (exactCountPathWeight hN S hM0)
    (fun z => exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
      ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))
    (fun z => 2 * exactCountM₀ N + exactCountGrid N
      ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
      ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) ?_ ?_ ?_
  · exact (show (1 : ℕ) ≤ 2 by omega).trans hM0
  · intro z
    exact (show (1 : ℕ) ≤ 2 by omega).trans (hM z)
  · intro z
    exact exactCount_sourceLedger_eq N z

theorem basicApproxCount_expected_source_eq_marks_plus_finals (N : ℕ) (S : Finset (Fin N))
    (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) * ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ))
      = (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((basicApproxCountExecutedGrids N ε ω).length : ℝ) := by
  have h := (basicApproxCount_oracle_cost_transport N S hN ε hε).2.1
  dsimp [ExpectedLedgerTransport] at h
  have hc : (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) * ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ))
      = (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) *
          ((recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
            (basicApproxCountExecFlag N ω)
            (basicApproxCountFinalM ε (basicApproxCountStop N ω))).sum : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [basicApproxCount_sourceLedger_eq N ε ω]
  exact hc.trans h.1

theorem basicApproxCount_expected_ledger_slots (N : ℕ) (S : Finset (Fin N))
    (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) *
          ((pathPrep (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
      = 2 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((basicApproxCountExecutedGrids N ε ω).length : ℝ) ∧
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) *
          ((pathControl (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
      = ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ) ∧
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) * (0 : ℝ)) = 0 ∧
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
        (basicApproxCountPrefixWeight hN S ω) *
          ((pathFixed (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
      = 5 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        + 3 * ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN S ω) *
            ((basicApproxCountExecutedGrids N ε ω).length : ℝ) := by
  have h := (basicApproxCount_oracle_cost_transport N S hN ε hε).2.1
  dsimp [ExpectedLedgerTransport] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem exactCount_expected_source_eq_marks_plus_finals (N : ℕ) (S : Finset (Fin N))
    (hN : 0 < N) (hM0 : 2 ≤ exactCountM₀ N)
    (hM : ∀ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) :
    (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
        (exactCountPathWeight hN S hM0 z) *
          ((2 * exactCountM₀ N + exactCountGrid N
            ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
            ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2) : ℕ) : ℝ))
      = (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
          (exactCountPathWeight hN S hM0 z) *
            ((pathMarks (exactCountExecutedGrids N z) : ℕ) : ℝ))
        + ∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
          (exactCountPathWeight hN S hM0 z) *
            ((exactCountExecutedGrids N z).length : ℝ) := by
  have h := (exactCount_oracle_cost_transport N S hN hM0 hM).2.1
  dsimp [ExpectedLedgerTransport] at h
  have hc : (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
        (exactCountPathWeight hN S hM0 z) *
          ((2 * exactCountM₀ N + exactCountGrid N
            ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
            ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2) : ℕ) : ℝ))
      = (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
        (exactCountPathWeight hN S hM0 z) *
          ((recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
            (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
              ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))).sum : ℝ)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [exactCount_sourceLedger_eq N z]
  exact hc.trans h.1

def sourceRoundRecordGrid (M : ℕ) (j : Fin M) : ℕ := sourceDepth M j

def sourceRoundRecordLedger (M : ℕ) (j : Fin M) : OracleCostLedger :=
  recordLedger (sourceDepth M j)

theorem sourceRoundRecord_ledger_transport (M : ℕ) (j : Fin M) :
    RecordLedgerTransport (sourceDepth M j) (sourceRoundRecordLedger M j) := by
  have h1 : 1 ≤ sourceDepth M j := by
    rw [sourceDepth]
    omega
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show sourceDepth M j = (sourceDepth M j - 1) + 1
  exact Nat.sub_add_cancel h1

def sourceRoundSourceLedger (M : ℕ) : ℕ := ∑ j : Fin M, sourceDepth M j

def sourceRoundControlledMarkLedger (M : ℕ) : ℕ := ∑ j : Fin M, (sourceDepth M j - 1)

theorem sourceRound_ledger_relation (M : ℕ) :
    sourceRoundSourceLedger M = sourceRoundControlledMarkLedger M + M := by
  have hsub : ∀ j : Fin M, sourceDepth M j - 1 = j.val := by
    intro j
    simp [sourceDepth]
  have hsum : (∑ j : Fin M, sourceDepth M j) = (∑ j : Fin M, (j.val : ℕ)) + M := by
    have h1 : (∑ j : Fin M, sourceDepth M j) = ∑ j : Fin M, (j.val + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [h1, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  unfold sourceRoundSourceLedger sourceRoundControlledMarkLedger
  rw [hsum, Finset.sum_congr rfl (fun j _ => hsub j)]
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
