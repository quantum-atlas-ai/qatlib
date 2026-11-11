/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeResult

/-!
# Resource ledger recurrences for scheduled search

`Fee` indexes the five resource ledgers and a stage counter, with `ledger` and `increment`
describing total and single-stage charges. The expected charge satisfies a first-stage
recurrence, including the version for schedules that interleave a plain trial before every
amplification window.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `expected_cons`: Expected charge on a nonempty schedule equals the first-stage expected charge
  plus first-stage failure probability times the tail expected charge.
* `interleaved_expected_cons`: Expands the expected resource charge of an interleaved schedule
  into its plain stage, amplification stage, and surviving tail.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- The resource categories for phase queries, bits, validation queries, preparation calls,
macro gates, and search stages. -/
inductive Fee where
 | phase | bits | validation | prepare | gates | stages
 deriving DecidableEq,Fintype

/-- Selects the trace count for resource `f`, using the number of windows for the stage count. -/
def ledger {I:Type} (f:Fee) (tr:CappedSearchTrace I) : ℕ := match f with
 | .phase=>tr.phaseQueries | .bits=>tr.bits | .validation=>tr.validationQueries
 | .prepare=>tr.prepareCalls | .gates=>tr.macroGates | .stages=>tr.windows.length

/-- The contribution of one sampled outcome to the selected resource ledger. -/
def increment {I:Type} (f:Fee) (out:Option (I×ℕ)×ℕ×ℕ) : ℕ := match f with
 | .phase=>out.2.2 | .bits=>out.2.1 | .validation=>if out.1.isSome then 1 else 0
 | .prepare=>if out.1.isSome then 2*out.2.2+1 else 0
 | .gates=>(out.1.map fun y=>y.2).getD 0 | .stages=>1

/-- Prepending a search receipt adds its resource increment to the existing ledger. -/
theorem ledger_prepend {I:Type} (f:Fee) (m:ℕ) (out:Option (I×ℕ)×ℕ×ℕ) (tr:CappedSearchTrace I) :
    ledger f (prependSearchReceipt m out tr)=increment f out+ledger f tr := by
  cases f <;>simp [ledger,increment,prependSearchReceipt,Nat.add_comm]

/-- An empty search trace with a returned candidate has zero charge in every ledger. -/
theorem ledger_stop_zero {I:Type} (f:Fee) (y:I) : ledger f {emptySearchTrace with result:=some y}=0 := by
  cases f <;>simp [ledger,emptySearchTrace]
variable {I:Type} [Fintype I] [DecidableEq I]

/-- The extended nonnegative expected value of the selected resource ledger for scheduled
search. -/
def expected (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (ms:List ℕ) : ℝ≥0∞ :=
  expectation (searchForSchedule U hU seed S valid ms) (fun tr=>(ledger f tr:ℝ≥0∞))

/-- The expected single-stage resource increment for a sampled amplification window `m` with
three finite-coin attempts. -/
def slot (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (f:Fee) (m:ℕ) : ℝ≥0∞ :=
  expectation (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (fun out=>(increment f out:ℝ≥0∞))

/-- The probability that one sampled search stage fails validation or produces no candidate. -/
def fail (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (m:ℕ) : ℝ≥0∞ :=
  event (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (searchSlotFail valid)

/-- Expected charge on a nonempty schedule equals the first-stage expected charge plus
first-stage failure probability times the tail expected charge. -/
theorem expected_cons (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (m:ℕ) (ms:List ℕ) :
    expected U hU seed S valid f (m::ms)=slot U hU seed S f m+fail U hU seed S valid m*expected U hU seed S valid f ms := by
  exact search_ledger_recursion U hU seed S valid (ledger f) (increment f)
    (ledger_prepend f) (fun _ _ y=>ledger_stop_zero f y) m ms

/-- The expected resource charge of an empty schedule is zero. -/
theorem expected_nil (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) : expected U hU seed S valid f []=0 := by
  unfold expected searchForSchedule
  rw [expectation_pure]
  cases f <;>simp [ledger,emptySearchTrace]

/-- Replaces each window `m` in a schedule by the pair of windows `[1, m]`. -/
def interleavePlain (ms:List ℕ) : List ℕ := ms.flatMap (fun m=>[1,m])

/-- Expands the expected resource charge of an interleaved schedule into its plain stage,
amplification stage, and surviving tail. -/
theorem interleaved_expected_cons (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (m:ℕ) (ms:List ℕ) :
    expected U hU seed S valid f (interleavePlain (m::ms))=
      slot U hU seed S f 1+fail U hU seed S valid 1*(slot U hU seed S f m+
        fail U hU seed S valid m*expected U hU seed S valid f (interleavePlain ms)) := by
  simp only [interleavePlain,List.flatMap_cons,List.cons_append,List.nil_append,expected_cons]
end Qatlib.Papers.QAOAScaling23.SearchFees
