/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeResult

/-!
# Born-weight factorization of native search results

Validation identifies accepted point and success events with the corresponding sampled
marked-output events. The shared relative Born weight of a marked candidate survives both one
native stage and the first-success composition over an arbitrary search schedule.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `native_slot_factor`: With exact validation and marked mass `sin θ` squared for `0 < θ < π/2`,
  a marked candidate has native-stage mass equal to success mass times its relative prepared
  Born weight.
* `native_search_biased_law`: With exact validation and marked mass `sin θ` squared for `0 < θ <
  π/2`, every marked output mass of scheduled search equals total success mass times its
  relative prepared Born weight.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- For a candidate that passes validation, acceptance as `some i` is equivalent to the sampled
output containing `i` with some gate count. -/
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

/-- With exact marked-set validation, acceptance is equivalent to the sampled output containing
a marked candidate with some gate count. -/
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

/-- With exact validation and marked mass `sin θ` squared for `0 < θ < π/2`, a marked candidate
has native-stage mass equal to success mass times its relative prepared Born weight. -/
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

/-- With exact validation and marked mass `sin θ` squared for `0 < θ < π/2`, every marked output
mass of scheduled search equals total success mass times its relative prepared Born weight. -/
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
