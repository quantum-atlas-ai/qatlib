/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.MinimumCode

/-!
# Native strict-improvement search oracle

`strictMarked` and `strictValid` select candidates with cost strictly below the current cost.
The clocked oracle `oracleCode` returns the validated result of native scheduled search, has no
save instructions, and preserves the exact joint result-charge law.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `searchCode_sound`: Every candidate returned by `searchCode` passes the supplied validation
  test.
* `oracleCode_paid_law`: The joint result-charge law of the strict-improvement oracle equals
  native scheduled search mapped to its optional result and `searchFee`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- The finite set of candidates whose cost is strictly smaller than the current cost. -/
def strictMarked (cost : I → ℝ) (current : I) : Finset I :=
  Finset.univ.filter (fun i => cost i<cost current)

/-- The Boolean test that a candidate has cost strictly smaller than the current cost. -/
def strictValid (cost : I → ℝ) (current : I) (i : I) : Bool := decide (cost i<cost current)
omit [DecidableEq I] in

/-- The strict-improvement test returns true exactly on the strict marked set. -/
theorem strictValid_correct (cost : I → ℝ) (current i : I) :
    strictValid cost current i=true ↔ i∈strictMarked cost current := by simp [strictValid,strictMarked]

/-- Every candidate returned by `searchCode` passes the supplied validation test. -/
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

/-- Runs scheduled search for a strictly cheaper candidate and returns the optional result. -/
def oracleCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) : Code I (Option I) :=
  mapCode CappedSearchTrace.result
    (searchCode U hU seed (strictMarked cost current) (strictValid cost current) ms)

/-- The strict-improvement oracle contains no save instructions. -/
theorem oracleCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) :
    NoSave (oracleCode U hU seed cost ms current) :=
  (noSave_mapCode _ _).2 (searchCode_noSave U hU seed _ _ ms)

/-- The joint result-charge law of the strict-improvement oracle equals native scheduled search
mapped to its optional result and `searchFee`. -/
theorem oracleCode_paid_law (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (cost : I → ℝ) (ms : List ℕ) (current : I) :
    (paidTree cost current (oracleCode U hU seed cost ms current)).law=
      (searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) ms).map
        (fun tr => (tr.result,searchFee tr)) := by
  rw [oracleCode,paidTree_mapCode_law,native_search_paid_law,PMF.map_comp]
  rfl
end Qatlib.Papers.QAOAScaling23.CausalSearch
