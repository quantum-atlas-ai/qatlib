/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeResult
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

theorem accepted_point {I : Type} [DecidableEq I] (valid : I→Bool) (i : I)
    (hi : valid i=true) (out : Option (I×ℕ)×ℕ×ℕ) :
    acceptedResult valid out=some i ↔∃g,out.1=some (i,g) := by
  rcases out with ⟨a,b,c⟩
  cases a with
  | none => simp [acceptedResult]
  | some yg =>
    rcases yg with ⟨y,g⟩
    by_cases hy : y=i
    · subst y
      simp [acceptedResult,hi]
    · by_cases hv : valid y=true
      · simp [acceptedResult,hv,hy]
      · simp [acceptedResult,hv,hy]

theorem accepted_some {I : Type} (valid : I→Bool) (S : Finset I)
    (hvalid : ∀i,valid i=true ↔ i∈S) (out : Option (I×ℕ)×ℕ×ℕ) :
    (acceptedResult valid out).isSome ↔∃y g,out.1=some (y,g) ∧ y∈S := by
  rcases out with ⟨a,b,c⟩
  cases a with
  | none => simp [acceptedResult]
  | some yg =>
    rcases yg with ⟨y,g⟩
    by_cases hv : valid y=true
    · have hy := (hvalid y).mp hv
      simp [acceptedResult,hv,hy]
    · have hy : y∉S := fun h=>(hv ((hvalid y).mpr h))
      simp [acceptedResult,hv,hy]

theorem native_slot_factor {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I→Bool) (hvalid : ∀y,valid y=true ↔ y∈S)
    (θ : ℝ) (hθ0 : 0<θ) (hθ1 : θ<Real.pi/2)
    (hmass : MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (m : ℕ) (i : I) (hi : i∈S) :
    nativeResult U hU seed S valid m (some i)=
      event (nativeResult U hU seed S valid m) (fun x=>x.isSome)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  calc
    nativeResult U hU seed S valid m (some i)=
        event (nativeResult U hU seed S valid m) (fun x=>x=some i) := (event_point _ _).symm
    _=event (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (fun z=>∃g,z.1=some (i,g)) := by
      rw [nativeResult,event_map]
      exact event_congr (accepted_point valid i ((hvalid i).mpr hi))
    _=event (preparedAASampled U hU seed S (Nat.clog 2 m) m 3)
        (fun z=>∃y g,z.1=some (y,g) ∧ y∈S)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) :=
      sampled_biased_law U hU seed S θ hθ0 hθ1 hmass _ _ _ i hi
    _=_ := by
      rw [nativeResult,event_map]
      congr 1
      exact (event_congr (accepted_some valid S hvalid)).symm

theorem native_search_biased_law {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I→Bool) (hvalid : ∀y,valid y=true ↔ y∈S)
    (θ : ℝ) (hθ0 : 0<θ) (hθ1 : θ<Real.pi/2)
    (hmass : MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (ms : List ℕ) (i : I) (hi : i∈S) :
    event (searchForSchedule U hU seed S valid ms) (fun tr=>tr.result=some i)=
      event (searchForSchedule U hU seed S valid ms) (fun tr=>tr.result.isSome)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  let p := searchForSchedule U hU seed S valid ms
  calc
    event p (fun tr=>tr.result=some i)=(p.map CappedSearchTrace.result) (some i) := by
      rw [← event_map p CappedSearchTrace.result (fun x=>x=some i),event_point]
    _=event (p.map CappedSearchTrace.result) (fun x=>x.isSome)*
        ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
      change (searchForSchedule U hU seed S valid ms).map CappedSearchTrace.result (some i)=_
      rw [native_result_marginal]
      exact firstResult_factor _ ms i _
          (fun m=>native_slot_factor U hU seed S valid hvalid θ hθ0 hθ1 hmass m i hi)
    _=_ := by rw [event_map]
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
