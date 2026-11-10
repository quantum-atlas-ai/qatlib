/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.ResultFactor
import Qatlib.Papers.QAOAScaling23.SearchFees.PlainSlot
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive
variable {I : Type} [Fintype I] [DecidableEq I]

theorem native_none_failure (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I→Bool) (m : ℕ) :
    Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid m none=Qatlib.Papers.QAOAScaling23.SearchFees.fail U hU seed S valid m := by
  rw [← Qatlib.Papers.QAOAScaling23.SearchPrimitive.event_point,Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult,event_map]
  apply event_congr
  intro out
  rcases out with ⟨a,b,c⟩
  cases a with
  | none => simp [Qatlib.Papers.QAOAScaling23.SearchPrimitive.acceptedResult,searchSlotFail]
  | some yg =>
    rcases yg with ⟨y,g⟩
    by_cases hy : valid y=true <;> simp [Qatlib.Papers.QAOAScaling23.SearchPrimitive.acceptedResult,searchSlotFail,hy]

theorem native_plain_point (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I→Bool) (hvalid : ∀y,valid y=true↔y∈S)
    (i : I) (hi : i∈S) :
    Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid 1 (some i)=ENNReal.ofReal (BornProb (preparedAAState U seed) i) := by
  rw [← Qatlib.Papers.QAOAScaling23.SearchPrimitive.event_point,Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult,event_map]
  exact (event_congr (Qatlib.Papers.QAOAScaling23.SearchPrimitive.accepted_point valid i ((hvalid i).mpr hi))).trans
    (Qatlib.Papers.QAOAScaling23.SearchFees.plain_candidate_point U hU seed S i)

theorem native_search_Q_one_point (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I→Bool) (hvalid : ∀y,valid y=true↔y∈S)
    (hQ : MeasureProb (preparedAAState U seed) S=1) (ms : List ℕ) (i : I) (hi : i∈S) :
    event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result=some i)=
      ENNReal.ofReal (BornProb (preparedAAState U seed) i) := by
  have hz : Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid 1 none=0 := by
    rw [native_none_failure,Qatlib.Papers.QAOAScaling23.SearchFees.plain_Q_one U hU seed S valid hvalid hQ]
  calc
    _=((searchForSchedule U hU seed S valid (1::ms)).map CappedSearchTrace.result) (some i) := by
      rw [← event_map _ CappedSearchTrace.result (fun x=>x=some i),Qatlib.Papers.QAOAScaling23.SearchPrimitive.event_point]
    _=_ := by
      rw [Qatlib.Papers.QAOAScaling23.SearchPrimitive.native_result_marginal,Qatlib.Papers.QAOAScaling23.SearchPrimitive.firstResult,Qatlib.Papers.QAOAScaling23.SearchPrimitive.firstBind_point,hz,
        zero_mul,add_zero,native_plain_point U hU seed S valid hvalid i hi]

theorem native_search_Q_one_success (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I→Bool) (hvalid : ∀y,valid y=true↔y∈S)
    (hQ : MeasureProb (preparedAAState U seed) S=1) (ms : List ℕ) :
    event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result.isSome)=1 := by
  have hz : Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid 1 none=0 := by
    rw [native_none_failure,Qatlib.Papers.QAOAScaling23.SearchFees.plain_Q_one U hU seed S valid hvalid hQ]
  have hc :=
      event_compl (Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid 1)
      (fun x=>x=none)
  rw [Qatlib.Papers.QAOAScaling23.SearchPrimitive.event_point,hz,zero_add] at hc
  have hp : event (Qatlib.Papers.QAOAScaling23.SearchPrimitive.nativeResult U hU seed S valid 1) (fun x=>x.isSome)=1 := by
    convert hc using 1
    apply event_congr
    intro x
    cases x <;>simp
  rw [← event_map _ CappedSearchTrace.result (fun x=>x.isSome),Qatlib.Papers.QAOAScaling23.SearchPrimitive.native_result_marginal,
    Qatlib.Papers.QAOAScaling23.SearchPrimitive.firstResult,Qatlib.Papers.QAOAScaling23.SearchPrimitive.firstBind_success,hp,hz,zero_mul,add_zero]

theorem native_search_Q_one_biased_law (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (valid : I→Bool) (hvalid : ∀y,valid y=true↔y∈S)
    (hQ : MeasureProb (preparedAAState U seed) S=1) (ms : List ℕ) (i : I) (hi : i∈S) :
    event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result=some i)=
      event (searchForSchedule U hU seed S valid (1::ms)) (fun tr=>tr.result.isSome)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  rw [native_search_Q_one_point U hU seed S valid hvalid hQ ms i hi,
    native_search_Q_one_success U hU seed S valid hvalid hQ ms,hQ,div_one,one_mul]
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
