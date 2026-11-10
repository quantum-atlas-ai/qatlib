/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeClass
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Born

theorem finite_event_sum {A : Type} [Fintype A] (p : PMF A) (P : A → Prop) [DecidablePred P] :
    (∑ a, if P a then p a else 0) = event p P := by
  unfold event expectation
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem indexed_event {A : Type} (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree A) (P : A → Prop) [DecidablePred P] :
    event (Tree.indexedLeafLaw t) (fun a => P (Tree.indexedLeafValue t a)) = event t.law P := by
  rw [← event_map,Tree.indexedLeafLaw_value]

theorem finite_local_law {K L : ℕ} (p : PMF (Fin K)) (output : Fin K → Option (Fin L))
    (target : PMF (Fin L)) (s : ℝ≥0∞)
    (hpoint : ∀j,event p (fun a => output a = some j) = s * target j) :
    ∀j,(∑a,if output a = some j then p a else 0) =
      (∑a,if (output a).isSome then p a else 0) * target j := by
  have hs : event p (fun a => (output a).isSome) = s := by
    rw [option_success_sum]
    simp_rw [hpoint]
    rw [← Finset.mul_sum]
    have ht := target.tsum_coe
    rw [tsum_fintype] at ht
    rw [ht,mul_one]
  intro j
  rw [finite_event_sum,finite_event_sum,hpoint,hs]
variable {I : Type} [Fintype I] [DecidableEq I]

theorem native_equal_rank_point (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (k : ℕ) (hk : k ≤ (costLevels cost).card)
    (hr : k = (costRank cost current).val)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) k)
    (ms : List ℕ) (j : Fin k) :
    let p :=
        searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms)
    event p (fun tr => tr.result.bind (lowerRank cost k) = some j) =
      event p (fun tr => tr.result.isSome) * lowerClassLaw cost (preparedLaw U hU seed) k hk hpos j := by
  subst k
  exact native_class_point U hU seed cost current hpos ms j

theorem native_rank_point (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (r+1))
    (ms : List ℕ) (j : Fin (r+1)) :
    let p :=
        searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms)
    event p (fun tr => tr.result.bind (lowerRank cost (r+1)) = some j) =
      event p (fun tr => tr.result.isSome) *
        lowerClassLaw cost (preparedLaw U hU seed) (r+1) (by omega) hpos j := by
  exact native_equal_rank_point U hU seed cost current (r+1) (by omega) hr.symm hpos ms j

theorem native_leaf_local (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (r+1)) (ms : List ℕ)
    (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (CappedSearchTrace I))
    (ht : t.law = searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms)) :
    ∀j,(∑a,if (Tree.indexedLeafValue t a).result.bind (lowerRank cost (r+1)) = some j then Tree.indexedLeafLaw t a else 0) =
      (∑a,if ((Tree.indexedLeafValue t a).result.bind (lowerRank cost (r+1))).isSome then Tree.indexedLeafLaw t a else 0) *
        lowerClassLaw cost (preparedLaw U hU seed) (r+1) (by omega) hpos j := by
  apply finite_local_law
  intro j
  rw [indexed_event t (fun tr => tr.result.bind (lowerRank cost (r+1)) = some j),ht]
  exact native_rank_point U hU seed cost current r hr hpos ms j

def nativeCompletedRow (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (r+1))
    (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (CappedSearchTrace I)) (fee : CappedSearchTrace I → ℕ) : Row r :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row (Tree.indexedLeafLaw t)
    (fun a => (Tree.indexedLeafValue t a).result.bind (lowerRank cost (r+1)))
    (fun a => fee (Tree.indexedLeafValue t a))
    (lowerClassLaw cost (preparedLaw U hU seed) (r+1) (by omega) hpos)

theorem native_completed_next_real (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (r+1)) (ms : List ℕ)
    (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (CappedSearchTrace I))
    (ht : t.law = searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms))
    (fee : CappedSearchTrace I → ℕ) (j : Fin (r+1)) :
    let row := nativeCompletedRow U hU seed cost current r hr hpos t fee
    (∑a,if row.next a = j then (row.law a).toReal else 0) =
      weights cost (preparedLaw U hU seed) j.val / prefixSum (weights cost (preparedLaw U hU seed)) (r+1) := by
  change _ = _
  rw [← lowerClassLaw_real cost (preparedLaw U hU seed) (r+1) (by omega) hpos j]
  exact Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row_next_real _ _ _ _
      (native_leaf_local U hU seed cost current r hr hpos ms t ht) j
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
