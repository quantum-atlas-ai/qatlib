/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeResult
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees

inductive Fee where
 | phase | bits | validation | prepare | gates | stages
 deriving DecidableEq,Fintype

def ledger {I:Type} (f:Fee) (tr:CappedSearchTrace I) : ℕ := match f with
 | .phase=>tr.phaseQueries | .bits=>tr.bits | .validation=>tr.validationQueries
 | .prepare=>tr.prepareCalls | .gates=>tr.macroGates | .stages=>tr.windows.length

def increment {I:Type} (f:Fee) (out:Option (I×ℕ)×ℕ×ℕ) : ℕ := match f with
 | .phase=>out.2.2 | .bits=>out.2.1 | .validation=>if out.1.isSome then 1 else 0
 | .prepare=>if out.1.isSome then 2*out.2.2+1 else 0
 | .gates=>(out.1.map fun y=>y.2).getD 0 | .stages=>1

theorem ledger_prepend {I:Type} (f:Fee) (m:ℕ) (out:Option (I×ℕ)×ℕ×ℕ) (tr:CappedSearchTrace I) :
    ledger f (prependSearchReceipt m out tr)=increment f out+ledger f tr := by
  cases f <;>simp [ledger,increment,prependSearchReceipt,Nat.add_comm]

theorem ledger_stop_zero {I:Type} (f:Fee) (y:I) : ledger f {emptySearchTrace with result:=some y}=0 := by
  cases f <;>simp [ledger,emptySearchTrace]
variable {I:Type} [Fintype I] [DecidableEq I]

def expected (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (ms:List ℕ) : ℝ≥0∞ :=
  expectation (searchForSchedule U hU seed S valid ms) (fun tr=>(ledger f tr:ℝ≥0∞))

def slot (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (f:Fee) (m:ℕ) : ℝ≥0∞ :=
  expectation (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (fun out=>(increment f out:ℝ≥0∞))

def fail (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (m:ℕ) : ℝ≥0∞ :=
  event (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (searchSlotFail valid)

theorem expected_cons (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (m:ℕ) (ms:List ℕ) :
    expected U hU seed S valid f (m::ms)=slot U hU seed S f m+fail U hU seed S valid m*expected U hU seed S valid f ms := by
  exact search_ledger_recursion U hU seed S valid (ledger f) (increment f)
    (ledger_prepend f) (fun _ _ y=>ledger_stop_zero f y) m ms

theorem expected_nil (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) : expected U hU seed S valid f []=0 := by
  unfold expected searchForSchedule
  rw [expectation_pure]
  cases f <;>simp [ledger,emptySearchTrace]

def interleavePlain (ms:List ℕ) : List ℕ := ms.flatMap (fun m=>[1,m])

theorem interleaved_expected_cons (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (m:ℕ) (ms:List ℕ) :
    expected U hU seed S valid f (interleavePlain (m::ms))=
      slot U hU seed S f 1+fail U hU seed S valid 1*(slot U hU seed S f m+
        fail U hU seed S valid m*expected U hU seed S valid f (interleavePlain ms)) := by
  simp only [interleavePlain,List.flatMap_cons,List.cons_append,List.nil_append,expected_cons]
end Qatlib.Papers.QAOAScaling23.SearchFees
