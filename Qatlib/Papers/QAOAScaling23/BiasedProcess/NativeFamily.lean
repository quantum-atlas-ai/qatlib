/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.ActualRowFees
import Qatlib.Papers.QAOAScaling23.BiasedProcess.GlobalFallback
import Qatlib.Papers.QAOAScaling23.CausalSearch.PublicBudget

/-!
# A native oracle row family over all ranks

This module constructs a total family of descent rows and associated candidates, using actual
search rows at valid thresholds and fallback rows beyond the cost-class range. It proves the
weighted transition law and preserves the joint paid oracle law for the adaptive descent
protocol of [ShaydulinEtAl2024].

## Main statements

* `candidate_rank`: Every native family candidate has the rank recorded by its row's next state.
* `row_law`: The total native row family satisfies `RowLaw` for the prepared Born cost-class
  weights.
* `joint_paid`: For a current candidate of rank `r + 1`, the joint paid oracle law equals the
  native row law mapped through `rowPayload`. This connects the row family to the adaptive
  descent protocol of [ShaydulinEtAl2024].

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeFamily
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open CausalSearch WeightedCost BudgetPrefix
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- Candidates with equal cost ranks define the same strict marked predicate. -/
theorem marked_equal_rank (cost : I → ℝ) (x y : I)
    (h : (costRank cost x).val=(costRank cost y).val) : strictMarked cost x=strictMarked cost y := by
  have he : cost x=cost y := (costRank_eq_iff cost x y).mp (Fin.ext h)
  simp only [strictMarked,he]

omit [DecidableEq I] in

/-- Candidates with equal cost ranks define the same strict validity predicate. -/
theorem valid_equal_rank (cost : I → ℝ) (x y : I)
    (h : (costRank cost x).val=(costRank cost y).val) : strictValid cost x=strictValid cost y := by
  have he : cost x=cost y := (costRank_eq_iff cost x y).mp (Fin.ext h)
  funext i
  simp only [strictValid,he]

/-- Candidates with equal cost ranks yield the same joint paid oracle law for a fixed
preparation and schedule. -/
theorem paid_equal_rank (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (ms : List ℕ) (x y : I)
    (h : (costRank cost x).val=(costRank cost y).val) :
    (paidTree cost x (oracleCode U hU seed cost ms x)).law=
      (paidTree cost y (oracleCode U hU seed cost ms y)).law := by
  rw [oracleCode_paid_law,oracleCode_paid_law,marked_equal_rank cost x y h,valid_equal_rank cost x y h]

/-- Positive optimal-class weight makes every positive-length prepared class-weight prefix
strictly positive. -/
theorem actual_prefix_pos (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (r : ℕ) :
    0<prefixSum (Born.weights cost (Born.preparedLaw U hU seed)) (r+1) :=
  prefix_positive _ h0 (Born.weights_nonneg cost _) _ (Nat.succ_pos r)

/-- A chosen candidate of rank `r + 1` when that rank lies in the cost-class range. -/
def threshold (cost : I → ℝ) (r : ℕ) (hr : r+1<(costLevels cost).card) : I :=
  Outside.classRep cost ⟨r+1,hr⟩

omit [DecidableEq I] in

/-- The chosen threshold candidate has rank value `r + 1`. -/
theorem threshold_rank (cost : I → ℝ) (r : ℕ) (hr : r+1<(costLevels cost).card) :
    (costRank cost (threshold cost r hr)).val=r+1 :=
  congrArg Fin.val (Outside.classRep_rank cost ⟨r+1,hr⟩)

/-- A row paired with its candidate map, using the actual native threshold row in range and the
fallback row otherwise. -/
def entry (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ) :
    Σ row : Row r,Fin row.outcomes → I :=
  if hr : r+1<(costLevels cost).card then
    ⟨NativeRows.actualRow U hU seed cost (threshold cost r hr) r (threshold_rank cost r hr)
      (actual_prefix_pos U hU seed cost h0 r) ms,
      NativeRows.actualCandidate U hU seed cost (threshold cost r hr) r (threshold_rank cost r hr)
      (actual_prefix_pos U hU seed cost h0 r) ms⟩
  else ⟨Outside.fallbackRow cost (Born.preparedLaw U hU seed) r (Nat.le_of_not_gt hr),Outside.classRep cost⟩

/-- At a rank inside the cost-class range, the family entry is the actual row and candidate map
for the chosen threshold. -/
theorem entry_actual (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ)
    (hr : r+1<(costLevels cost).card) : entry U hU seed cost h0 ms r=
    ⟨NativeRows.actualRow U hU seed cost (threshold cost r hr) r (threshold_rank cost r hr)
      (actual_prefix_pos U hU seed cost h0 r) ms,
      NativeRows.actualCandidate U hU seed cost (threshold cost r hr) r (threshold_rank cost r hr)
      (actual_prefix_pos U hU seed cost h0 r) ms⟩ := by
  unfold entry
  exact dif_pos hr

/-- Outside the actual threshold range, the family entry is the fallback row with its class
representatives. -/
theorem entry_outside (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ)
    (hr : ¬r+1<(costLevels cost).card) : entry U hU seed cost h0 ms r=
    ⟨Outside.fallbackRow cost (Born.preparedLaw U hU seed) r (Nat.le_of_not_gt hr),Outside.classRep cost⟩ := by
  unfold entry
  exact dif_neg hr

/-- The descent row component of the total native family at rank index `r`. -/
def rows (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ) : Row r :=
  (entry U hU seed cost h0 ms r).1

/-- The candidate map component of the total native family at rank index `r`. -/
def candidate (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ)
    (a : Fin (rows U hU seed cost h0 ms r).outcomes) : I :=
  (entry U hU seed cost h0 ms r).2 a

/-- Every native family candidate has the rank recorded by its row's next state. -/
theorem candidate_rank (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (r : ℕ)
    (a : Fin (rows U hU seed cost h0 ms r).outcomes) :
    (costRank cost (candidate U hU seed cost h0 ms r a)).val=
      ((rows U hU seed cost h0 ms r).next a).val := by
  revert a
  unfold rows candidate
  by_cases hr : r+1<(costLevels cost).card
  · rw [entry_actual U hU seed cost h0 ms r hr]
    intro a
    exact NativeRows.actual_candidate_rank U hU seed cost
      (threshold cost r hr) r (threshold_rank cost r hr) (actual_prefix_pos U hU seed cost h0 r) ms a
  · rw [entry_outside U hU seed cost h0 ms r hr]
    intro a
    exact Outside.fallback_candidate_rank cost (Born.preparedLaw U hU seed) r
        (Nat.le_of_not_gt hr) a

/-- The total native row family satisfies `RowLaw` for the prepared Born cost-class weights. -/
theorem row_law (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) :
    RowLaw (Born.weights cost (Born.preparedLaw U hU seed)) (rows U hU seed cost h0 ms) := by
  intro r j
  unfold rows
  by_cases hr : r+1<(costLevels cost).card
  · rw [entry_actual U hU seed cost h0 ms r hr]
    exact NativeRows.actual_row_next U hU seed cost (threshold cost r hr)
      r (threshold_rank cost r hr) (actual_prefix_pos U hU seed cost h0 r) ms j
  · rw [entry_outside U hU seed cost h0 ms r hr]
    exact Outside.fallback_row_law cost (Born.preparedLaw U hU seed)
      r (Nat.le_of_not_gt hr) j

/-- For a current candidate of rank `r + 1`, the joint paid oracle law equals the native row law
mapped through `rowPayload`. This connects the row family to the adaptive descent protocol
of [ShaydulinEtAl2024]. -/
theorem joint_paid (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (ms : List ℕ) (current : I)
    (r : ℕ) (hcurrent : (costRank cost current).val=r+1) :
    (paidTree cost current (oracleCode U hU seed cost (1::ms) current)).law=
      (rows U hU seed cost h0 ms r).law.map (rowPayload (rows U hU seed cost h0 ms)
        (candidate U hU seed cost h0 ms) r) := by
  have hr : r+1<(costLevels cost).card := by rw [← hcurrent]; exact (costRank cost current).isLt
  rw [paid_equal_rank U hU seed cost (1::ms) current (threshold cost r hr)
    (hcurrent.trans (threshold_rank cost r hr).symm)]
  unfold rowPayload rows candidate
  rw [entry_actual U hU seed cost h0 ms r hr]
  exact NativeRows.actual_joint_paid U hU seed cost
    (threshold cost r hr) r (threshold_rank cost r hr) (actual_prefix_pos U hU seed cost h0 r) ms
end Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeFamily
