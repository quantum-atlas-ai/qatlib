/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.TimeVaryHybrid
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

theorem sourceEditSchedule_length (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool) :
    (sourceEditSchedule T A U F answer).length = T := by
  simp [sourceEditSchedule]

theorem sourceEditSchedule_unitary (T : ℕ) (A : I → Bool)
    (U : Fin T → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (F : Fin T → Finset I) (answer : Fin T → I → Bool) :
    ∀ e ∈ sourceEditSchedule T A U F answer,
      e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := by
  intro e he
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
  exact hU t

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
