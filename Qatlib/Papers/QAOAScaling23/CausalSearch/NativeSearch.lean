/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeSampled
import Qatlib.Concepts.WalkSearch.QuantumAccess.CappedGeometricSearch

/-!
# Clocked native scheduled search

`searchCode` executes the scheduled sampled amplification trials and charges for validation of
each produced candidate. Its native trace law and exact fee agree with the clocked execution,
while transcript replay describes every budgeted prefix and the saved candidate stays unchanged.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `searchCode_actual_law`: The value law of `searchCode` equals the native `searchForSchedule`
  law.
* `native_search_online_prefix`: Replaying complete search transcripts with budget `B` has the
  same law as running the search code online with that budget.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of bit, phase-query, validation-query, preparation-call, and macro-gate counts in a
search trace. -/
def searchFee (tr : CappedSearchTrace I) : ℕ :=
  tr.bits+tr.phaseQueries+tr.validationQueries+tr.prepareCalls+tr.macroGates

/-- Executes sampled trials along a schedule, paying for validation and stopping at the first
candidate that passes the validation test. -/
def searchCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) : List ℕ → Code I (CappedSearchTrace I)
  | [] => .ret emptySearchTrace
  | m::ms => bindCode (sampledCode U hU seed S (Nat.clog 2 m) m 3) (fun out =>
      match out.1 with
      | none => mapCode (prependSearchReceipt m out) (searchCode U hU seed S valid ms)
      | some yg => .pay 1 (if valid yg.1 then
          .ret (prependSearchReceipt m out {emptySearchTrace with result:=some yg.1})
        else mapCode (prependSearchReceipt m out) (searchCode U hU seed S valid ms)))

/-- The value law of `searchCode` equals the native `searchForSchedule` law. -/
theorem searchCode_actual_law (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    valueLaw cost current (searchCode U hU seed S valid ms)=searchForSchedule U hU seed S valid ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [searchCode,valueLaw_bindCode cost current _ (sampledCode_noSave U hU seed S _ _ _),sampledCode_actual_law]
    change (preparedAASampled U hU seed S (Nat.clog 2 m) m 3).bind _ =
      (preparedAASampled U hU seed S (Nat.clog 2 m) m 3).bind _
    congr 1
    funext out
    cases ho : out.1 with
    | none => simp only [valueLaw_mapCode,ih]; rfl
    | some yg =>
      cases hv : valid yg.1 with
      | false =>
        simp only [valueLaw,hv,Bool.false_eq_true,if_false,valueLaw_mapCode,ih]
        rfl
      | true => simp only [valueLaw,hv,if_true]

/-- The scheduled search code contains no save instructions. -/
theorem searchCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    NoSave (searchCode U hU seed S valid ms) := by
  induction ms with
  | nil => trivial
  | cons m ms ih =>
    rw [searchCode]
    apply noSave_bindCode _ (sampledCode_noSave U hU seed S _ _ _)
    intro out
    cases ho : out.1 with
    | none => exact (noSave_mapCode _ _).2 ih
    | some yg =>
      change NoSave (if valid yg.1 then _ else _)
      split_ifs
      · trivial
      · exact (noSave_mapCode _ _).2 ih

omit [Fintype I] [DecidableEq I] in

/-- Prepending a search receipt adds its sampled word fee and one validation charge exactly when
a candidate is present. -/
theorem prepend_searchFee (m : ℕ) (out : Option (I×ℕ)×ℕ×ℕ) (tr : CappedSearchTrace I) :
    searchFee (prependSearchReceipt m out tr)=sampledWordFee out+
      (if out.1.isSome then 1 else 0)+searchFee tr := by
  rcases out with ⟨o,bits,queries⟩
  cases o with
  | none => simp [prependSearchReceipt,searchFee,sampledWordFee]; ring
  | some yg => simp [prependSearchReceipt,searchFee,sampledWordFee]; ring

/-- Every returned search trace has paid charge equal to `searchFee`. -/
theorem searchCode_returns (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    Returns cost current (searchCode U hU seed S valid ms) (fun tr fee => fee=searchFee tr) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [searchCode]
    apply returns_bindCode cost current _ (sampledCode_noSave U hU seed S _ _ _)
    apply returns_mono _ _ _ (sampledCode_returns cost current U hU seed S _ _ _)
    intro out fee hfee
    cases ho : out.1 with
    | none =>
      rw [returns_mapCode]
      apply returns_mono _ _ _ ih
      intro tr tailFee htail
      rw [hfee,htail,prepend_searchFee]
      simp [ho]
    | some yg =>
      rw [Returns]
      split_ifs with hv
      · simp only [Returns,Nat.add_zero]
        rw [hfee,prepend_searchFee]
        simp [ho,searchFee,emptySearchTrace]
      · rw [returns_mapCode]
        apply returns_mono _ _ _ ih
        intro tr tailFee htail
        rw [hfee,htail,prepend_searchFee]
        simp [ho]
        omega

/-- Replaying complete search transcripts with budget `B` has the same law as running the search
code online with that budget. -/
theorem native_search_online_prefix (cost : I → ℝ) (current : I) (B : ℕ)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    (complete cost current (searchCode U hU seed S valid ms)).law.map (replay cost current B)=
      (run cost current B (searchCode U hU seed S valid ms)).law :=
  online_prefix_law _ _ _ _

/-- Every complete search transcript returns a trace whose search fee equals the transcript
cost. -/
theorem native_search_transcript (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    (complete cost current (searchCode U hU seed S valid ms)).All
      (fun es => ∃ tr,returnValue es=some tr ∧ transcriptCost es=searchFee tr) :=
  returns_complete _ _ _ _ (searchCode_returns cost current U hU seed S valid ms)

/-- Every budgeted scheduled-search result retains the initial saved candidate. -/
theorem native_search_saved_best (cost : I → ℝ) (current : I) (B : ℕ)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I → Bool) (ms : List ℕ) :
    (run cost current B (searchCode U hU seed S valid ms)).All (fun r => r.best=current) :=
  noSave_run_best _ _ _ _ (searchCode_noSave U hU seed S valid ms)
end Qatlib.Papers.QAOAScaling23.CausalSearch
