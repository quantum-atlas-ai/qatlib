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

/-!
# Oracle cost transport for counting records

This module relates the source cost of counting procedures to oracle cost ledgers for their
recorded grid sizes. It treats adaptive approximate counting and the two-pilot exact-counting
construction associated with [BrassardEtAl2002], expressing total source cost as mark cost plus
one contribution per executed grid.

The expected identities use the corresponding prefix or pilot-record weights. Additional
source-round ledgers record the relation between source depths and controlled-mark counts.

## Main statements

* `basicApproxCount_oracle_cost_transport`: transport for adaptive approximate-counting records.
* `exactCount_oracle_cost_transport`: transport for exact-counting pilot records.
* `basicApproxCount_expected_ledger_slots`: expected component ledger identities.
* `sourceRound_ledger_relation`: the source-round source and controlled-mark relation.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

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

/-- Summing the values retained from a list of optional natural numbers equals summing after
replacing each `none` by zero. -/
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

/-- The sum of the recorded grid list equals the sum of the grids whose execution flags are
true, plus the final grid `m`. -/
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

/-- The grid size `2 * 2^l` of approximate-counting loop stage `l`. -/
def basicApproxCountLoopGrid (l : ℕ) : ℕ := 2 * 2 ^ l

/-- The Boolean flag recording whether stage `l` precedes the stopping index of the prefix
record `ω`. -/
noncomputable def basicApproxCountExecFlag (N : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val))
    (l : Fin (basicApproxCountLoopCap N)) : Bool :=
  decide (l.val < basicApproxCountStop N ω)

/-- The list of grid sizes of executed approximate-counting stages, followed by the final grid. -/
noncomputable def basicApproxCountExecutedGrids (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : List ℕ :=
  recordGrids (fun l : Fin (basicApproxCountLoopCap N) => basicApproxCountLoopGrid l.val)
    (basicApproxCountExecFlag N ω)
    (basicApproxCountFinalM ε (basicApproxCountStop N ω))

/-- The approximate-counting total cost equals the sum of the grids recorded by its execution
flags and final stage. -/
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

/-- The executed-grid list unfolds to the loop grids selected by `basicApproxCountExecFlag`,
followed by the final grid. -/
theorem basicApproxCount_executedGrids_eq (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) :
    basicApproxCountExecutedGrids N ε ω
      = recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
        (basicApproxCountExecFlag N ω)
        (basicApproxCountFinalM ε (basicApproxCountStop N ω)) := rfl

/-- For positive accuracy parameter `ε`, the final approximate-counting grid has at least one
point. -/
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

/-- For positive `N` and `ε`, the approximate-counting prefix weights, recorded grids, and total
cost satisfy `JointRecordOracleCostTransport`. -/
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

/-- The list consisting of the two initial exact-counting grids and the final grid selected by
their amplitude estimates. -/
noncomputable def exactCountExecutedGrids (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) : List ℕ :=
  recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
    (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
      ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))

/-- The sum of the two initial exact-counting grid sizes and the selected final grid equals the
sum of the recorded grid list. -/
theorem exactCount_sourceLedger_eq (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) :
    2 * exactCountM₀ N + exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)
      = (recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
        (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2))).sum := by
  rw [recordGrids_sum]
  simp

/-- The executed exact-counting grids unfold to two initial grids and the final grid determined
by the two readouts. -/
theorem exactCount_executedGrids_eq (N : ℕ)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) :
    exactCountExecutedGrids N z
      = recordGrids (fun _ : Fin 2 => exactCountM₀ N) (fun _ => true)
        (exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) := rfl

/-- The product probability of the two initial amplitude-estimation readouts used by exact
counting. -/
noncomputable def exactCountPathWeight {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM0 : 2 ≤ exactCountM₀ N)
    (z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N)) : ℝ :=
  ((aeLaw (exactCountM₀ N) (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM0).prob z.1) *
  ((aeLaw (exactCountM₀ N) (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM0).prob z.2)

/-- When the initial and all selected final grids have at least two points, the exact-counting
path weights, executed grids, and source cost satisfy `JointRecordOracleCostTransport`. -/
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

/-- The expected approximate-counting source cost equals the expected mark count plus the
expected number of executed grids, for positive `N` and `ε`. -/
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

/-- For positive `N` and `ε`, the expected preparation count is twice the expected mark count
plus the expected grid count, the expected control count equals the expected mark count, and
the zero slot vanishes. The expected fixed count is five times the expected mark count plus
three times the expected grid count. -/
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

/-- Under the stated grid-validity hypotheses, the expected exact-counting source cost equals
the expected mark count plus the expected number of executed grids. -/
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

/-- The grid size associated with readout `j`, given by `sourceDepth M j`. -/
def sourceRoundRecordGrid (M : ℕ) (j : Fin M) : ℕ := sourceDepth M j

/-- The oracle cost ledger `recordLedger (sourceDepth M j)` for one source-round readout. -/
def sourceRoundRecordLedger (M : ℕ) (j : Fin M) : OracleCostLedger :=
  recordLedger (sourceDepth M j)

/-- The source-round record ledger satisfies `RecordLedgerTransport` for the depth selected by
`j`. -/
theorem sourceRoundRecord_ledger_transport (M : ℕ) (j : Fin M) :
    RecordLedgerTransport (sourceDepth M j) (sourceRoundRecordLedger M j) := by
  have h1 : 1 ≤ sourceDepth M j := by
    rw [sourceDepth]
    omega
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show sourceDepth M j = (sourceDepth M j - 1) + 1
  exact Nat.sub_add_cancel h1

/-- The sum of `sourceDepth M j` over all source-round readouts `j : Fin M`. -/
def sourceRoundSourceLedger (M : ℕ) : ℕ := ∑ j : Fin M, sourceDepth M j

/-- The sum of `sourceDepth M j - 1` over all source-round readouts `j : Fin M`. -/
def sourceRoundControlledMarkLedger (M : ℕ) : ℕ := ∑ j : Fin M, (sourceDepth M j - 1)

/-- The total source-round source ledger equals the total controlled-mark ledger plus `M`. -/
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
