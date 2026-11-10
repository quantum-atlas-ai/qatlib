/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.FirstResult
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

def acceptedResult {I : Type} (valid : I→Bool) (out : Option (I×ℕ)×ℕ×ℕ) : Option I :=
  out.1.bind fun y=>if valid y.1 then some y.1 else none

def nativeResult {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I→Bool) (m : ℕ) : PMF (Option I) :=
  (preparedAASampled U hU seed S (Nat.clog 2 m) m 3).map (acceptedResult valid)

theorem native_result_marginal {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I→Bool) (ms : List ℕ) :
    (searchForSchedule U hU seed S valid ms).map CappedSearchTrace.result=
      firstResult (nativeResult U hU seed S valid) ms := by
  induction ms with
  | nil => simp [searchForSchedule,firstResult,emptySearchTrace,PMF.pure_map]
  | cons m ms ih =>
    rw [searchForSchedule,PMF.map_bind,firstResult,firstBind,nativeResult,PMF.bind_map]
    apply congrArg (PMF.bind (preparedAASampled U hU seed S (Nat.clog 2 m) m 3))
    funext out
    rcases out with ⟨a,b,c⟩
    cases a with
    | none =>
      simp only [PMF.map_comp]
      exact ih
    | some yg =>
      rcases yg with ⟨y,g⟩
      by_cases hy : valid y=true
      · simp [acceptedResult,hy,PMF.pure_map,prependSearchReceipt]
      · simpa [hy,Function.comp_def,acceptedResult,PMF.map_comp,prependSearchReceipt] using! ih
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
