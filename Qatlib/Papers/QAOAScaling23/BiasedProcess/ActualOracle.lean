/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.JointPayload
import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeOracle

/-!
# Actual search oracles as completed descent rows

This module extracts receipt trees from the paid strict-threshold search code and constructs
`actualRow` by completing failed searches with lower-rank samples. It preserves the actual
candidate and charge jointly, connecting the executable oracle to the biased descent model used
for [ShaydulinEtAl2024].

## Main statements

* `actual_row_next`: The next-rank marginal of the actual completed row equals the prepared Born
  class weight divided by the lower-rank prefix mass.
* `actual_candidate_rank`: The candidate associated with an actual row outcome has the rank
  recorded by that row's next state.
* `actual_joint_paid`: The joint law of the actual oracle's optional candidate and fee equals
  the corresponding completed-row law, with bad outcomes mapped to no candidate.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeRows
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The tree of capped search receipts obtained by projecting the result component of the paid
strict-threshold search execution. -/
def receiptTree (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (ms : List ℕ) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (CappedSearchTrace I) :=
  (paidTree cost current (Qatlib.Papers.QAOAScaling23.CausalSearch.searchCode U hU seed
    (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid cost current) ms)).map Prod.fst

/-- The receipt tree has the law of the corresponding scheduled strict-threshold search. -/
theorem receiptTree_law (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (ms : List ℕ) :
    (receiptTree U hU seed cost current ms).law = searchForSchedule U hU seed
      (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid cost current) ms := by
  rw [receiptTree,Tree.law_map,paidTree_value_law,
    Qatlib.Papers.QAOAScaling23.CausalSearch.searchCode_actual_law]

/-- Every candidate returned by the receipt tree has strictly smaller cost than the current
candidate. -/
theorem receiptTree_sound (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (ms : List ℕ) :
    (receiptTree U hU seed cost current ms).All (fun tr => ∀i,tr.result = some i → cost i < cost current) := by
  rw [receiptTree,Tree.all_map]
  apply paidTree_returns cost current
    (Qatlib.Papers.QAOAScaling23.CausalSearch.searchCode U hU seed (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid cost current) ms)
    (fun (tr : CappedSearchTrace I) (_ : ℕ) => ∀i,tr.result = some i → cost i < cost current)
  apply returns_mono _ _ _
      (Qatlib.Papers.QAOAScaling23.CausalSearch.searchCode_sound cost current U hU seed _ _ ms)
  intro tr fee h i hi
  simpa [Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid] using h i hi

/-- Every successful indexed receipt has rank strictly below `r + 1` when the current candidate
has that rank. -/
theorem indexed_sound (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (ms : List ℕ) (r : ℕ) (hr : (costRank cost current).val = r+1) :
    ∀a i,(Tree.indexedLeafValue (receiptTree U hU seed cost current ms) a).result = some i →
      (costRank cost i).val < r+1 := by
  intro a i hi
  have h := Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.leafValue_all _ _ (receiptTree_sound U hU seed cost current ms)
    ((Fintype.equivFin (Tree.Leaves (receiptTree U hU seed cost current ms))).symm a)
  have hc : cost i < cost current := h i hi
  have hrank := (costRank_lt_iff cost i current).mpr hc
  change (costRank cost i).val < (costRank cost current).val at hrank
  rwa [hr] at hrank

/-- The completed descent row built from the actual receipt tree for schedule `1 :: ms`,
retaining the search fee. -/
def actualRow (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ) : Row r :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.nativeCompletedRow U hU seed cost current r hr hpos
    (receiptTree U hU seed cost current (1::ms)) Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee

/-- The candidate associated with an actual completed-row outcome, using the receipt result or a
representative of the completed rank. -/
def actualCandidate (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ)
    (a : Fin (actualRow U hU seed cost current r hr hpos ms).outcomes) : I :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Payload.candidate cost r (by omega)
    (Tree.indexedLeafLaw (receiptTree U hU seed cost current (1::ms)))
    (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)))
    (fun a => Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a))
    (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerClassLaw cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed) (r+1) (by omega) hpos) a

/-- The next-rank marginal of the actual completed row equals the prepared Born class weight
divided by the lower-rank prefix mass. -/
theorem actual_row_next (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ)
    (j : Fin (r+1)) :
    let row := actualRow U hU seed cost current r hr hpos ms
    (∑a,if row.next a = j then (row.law a).toReal else 0) =
      Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed) j.val /
        prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1) :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.native_completed_next_real U hU seed cost current r hr hpos ms _
    (receiptTree_law U hU seed cost current (1::ms)) _ j

/-- The candidate associated with an actual row outcome has the rank recorded by that row's next
state. -/
theorem actual_candidate_rank (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ)
    (a : Fin (actualRow U hU seed cost current r hr hpos ms).outcomes) :
    (costRank cost (actualCandidate U hU seed cost current r hr hpos ms a)).val =
      ((actualRow U hU seed cost current r hr hpos ms).next a).val :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Payload.candidate_rank cost r (by omega) _ _ _ _ (indexed_sound U hU seed cost current (1::ms) r hr) a

/-- The joint law of the actual oracle's optional candidate and fee equals the corresponding
completed-row law, with bad outcomes mapped to no candidate. -/
theorem actual_joint_paid (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ) :
    (paidTree cost current (Qatlib.Papers.QAOAScaling23.CausalSearch.oracleCode U hU seed cost (1::ms) current)).law =
      (actualRow U hU seed cost current r hr hpos ms).law.map (fun a =>
        (if (actualRow U hU seed cost current r hr hpos ms).bad a then none else
          some (actualCandidate U hU seed cost current r hr hpos ms a),
          (actualRow U hU seed cost current r hr hpos ms).charge a)) := by
  symm
  rw [Qatlib.Papers.QAOAScaling23.CausalSearch.oracleCode_paid_law]
  have h := Qatlib.Papers.QAOAScaling23.BiasedProcess.Payload.candidate_fee_joint cost r (by omega)
    (Tree.indexedLeafLaw (receiptTree U hU seed cost current (1::ms)))
    (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)))
    (fun a => Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a))
    (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerClassLaw cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed) (r+1) (by omega) hpos)
    (indexed_sound U hU seed cost current (1::ms) r hr)
  refine h.trans ?_
  change (Tree.indexedLeafLaw (receiptTree U hU seed cost current (1::ms))).map
    ((fun tr => (tr.result,Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee tr)) ∘
      Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms))) = _
  rw [← PMF.map_comp,Tree.indexedLeafLaw_value,receiptTree_law]
end Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeRows
