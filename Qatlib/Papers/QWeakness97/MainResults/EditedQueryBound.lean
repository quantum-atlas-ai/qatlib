/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.TimeVaryHybrid

/-!
# Bounds for time-dependent oracle edits

`sourceEditSchedule` packages a fixed reference Boolean oracle, a sequence of edited address
sets and replacement answers, and the matrices applied after the queries. The edit charges are
measured on the reference execution, even though the replacement answers and edited sets may
vary with time.

This module gives the corrected finite XOR-oracle estimate corresponding to the hybrid argument
in Theorem 3.3 of [BennettEtAl1997]. Unitary mixing yields squared final distance at most `4 *
T` times the total reference charge; a charge budget of `ε^2 / (4 * T)` therefore gives distance
at most `ε` when `T` is positive.

## Main statements

* `sourceEditSchedule_length` and `sourceEditSchedule_unitary` verify the schedule length and
  mixing assumptions.
* `theorem33_source_energy` proves the squared-distance energy bound.
* `theorem33_source_corrected` derives the distance bound from the corrected charge budget.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QWeakness97.MainResults
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Classical

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Form a length-`T` edit schedule whose reference oracle is `A`, whose replacement at time `t`
uses `answer t` on `F t` and `A` elsewhere, and whose query is followed by the matrix `U t`. -/
def sourceEditSchedule (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool) : List (OracleEdit I W) :=
  List.ofFn fun t =>
    { reference := A
      replacement := fun x => if x ∈ F t then answer t x else A x
      scope := F t
      agrees := by intro x hx; simp [hx]
      mixing := U t }

omit [Fintype I] [Fintype W] [DecidableEq W] in

/-- The schedule built from `T` time-indexed oracle edits has exactly `T` entries. -/
theorem sourceEditSchedule_length (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool) :
    (sourceEditSchedule T A U F answer).length = T := by
  simp [sourceEditSchedule]

/-- If every prescribed mixing matrix `U t` is unitary, every edit in the constructed schedule
has a unitary mixing matrix. -/
theorem sourceEditSchedule_unitary (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool) :
    ∀ e ∈ sourceEditSchedule T A U F answer,
      e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := by
  intro e he
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
  exact hU t

/-- For unitary mixing matrices, the squared Euclidean distance between the replacement-oracle
and reference-oracle runs is at most `4 * T` times the total edit charge measured along the
reference run. This is the energy form of the corrected finite XOR-oracle comparison
associated with Theorem 3.3 of [BennettEtAl1997]. -/
theorem theorem33_source_energy (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool)
    (ψ : QState ((I × Bool) × W)) :
    let L := sourceEditSchedule T A U F answer
    ‖toEuclidean_fromVec (runOracleEdits true L ψ - runOracleEdits false L ψ)‖ ^ 2 ≤
      4 * (T : ℝ) * (editCharges L ψ).sum := by
  simpa only [sourceEditSchedule_length] using
    time_varying_hybrid_energy (sourceEditSchedule T A U F answer)
      (sourceEditSchedule_unitary T A U hU F answer) ψ

/-- For positive `T`, unitary mixing, and nonnegative `ε`, a total reference charge at most `ε^2
/ (4 * T)` ensures that the replacement and reference runs end within Euclidean distance
`ε`. This gives the corrected budget form for the actual Boolean XOR-oracle primitive
corresponding to Theorem 3.3 of [BennettEtAl1997]. -/
theorem theorem33_source_corrected (T : ℕ) (hT : 0 < T) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool)
    (ψ : QState ((I × Bool) × W)) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : (editCharges (sourceEditSchedule T A U F answer) ψ).sum ≤
      ε ^ 2 / (4 * (T : ℝ))) :
    let L := sourceEditSchedule T A U F answer
    ‖toEuclidean_fromVec (runOracleEdits true L ψ - runOracleEdits false L ψ)‖ ≤ ε := by
  apply time_varying_hybrid_budget _
    (sourceEditSchedule_unitary T A U hU F answer) ψ
  · simpa only [sourceEditSchedule_length] using hT
  · exact hε
  · simpa only [sourceEditSchedule_length] using hbudget

end Qatlib.Papers.QWeakness97.MainResults
