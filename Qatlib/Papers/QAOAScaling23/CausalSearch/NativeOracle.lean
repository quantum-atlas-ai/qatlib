/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.MinimumCode
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Concepts.WalkSearch.QuantumAccess
variable {I : Type} [Fintype I] [DecidableEq I]

def strictMarked (cost : I → ℝ) (current : I) : Finset I :=
  Finset.univ.filter (fun i => cost i<cost current)

def strictValid (cost : I → ℝ) (current : I) (i : I) : Bool := decide (cost i<cost current)
omit [DecidableEq I] in

theorem strictValid_correct (cost : I → ℝ) (current i : I) :
    strictValid cost current i=true ↔ i∈strictMarked cost current := by simp [strictValid,strictMarked]

theorem searchCode_sound (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I → Bool) (ms : List ℕ) :
    Returns cost current (searchCode U hU seed S valid ms)
      (fun tr _ => ∀ i,tr.result=some i → valid i=true) := by
  induction ms with
  | nil => simp [searchCode,Returns,emptySearchTrace]
  | cons m ms ih =>
    rw [searchCode]
    apply returns_bindCode cost current _ (sampledCode_noSave U hU seed S _ _ _)
    apply returns_mono _ _ _ (sampledCode_returns cost current U hU seed S _ _ _)
    intro out fee _
    cases ho : out.1 with
    | none =>
      rw [returns_mapCode]
      apply returns_mono _ _ _ ih
      intro tr tailFee ht
      exact ht
    | some yg =>
      rw [Returns]
      split_ifs with hv
      · simp only [Returns]
        intro i hi
        have he : yg.1=i := Option.some.inj hi
        simpa only [he] using hv
      · rw [returns_mapCode]
        apply returns_mono _ _ _ ih
        intro tr tailFee ht
        exact ht

def oracleCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) : Code I (Option I) :=
  mapCode CappedSearchTrace.result
    (searchCode U hU seed (strictMarked cost current) (strictValid cost current) ms)

theorem oracleCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) :
    NoSave (oracleCode U hU seed cost ms current) :=
  (noSave_mapCode _ _).2 (searchCode_noSave U hU seed _ _ ms)

theorem oracleCode_paid_law (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) :
    (paidTree cost current (oracleCode U hU seed cost ms current)).law=
      (searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) ms).map
        (fun tr => (tr.result,searchFee tr)) := by
  rw [oracleCode,paidTree_mapCode_law,native_search_paid_law,PMF.map_comp]
  rfl
end Qatlib.Papers.QAOAScaling23.CausalSearch
