/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReflectQuery10.MainResults.QueryComparisonReflectionDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.Reflections

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.ReflectQuery10.MainResults

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable {X : Type} [Fintype X] [DecidableEq X]

theorem clause85_complete (n m : ℕ) (hn : 0 < n)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ)
    (hv : SourceDualFeasible input f v W) (hW : 1 ≤ W) :
    ∃ (r : ℕ) (hr : 0 < r) (P : SourceProgram X),
      IsUnitaryCircuit P.circuit ∧
        QueryCount P.circuit ≤ 1000000 * Nat.ceil W ∧
        GateCount P.circuit ≤ 10000000 * Nat.ceil W ∧
        P.DecidesWithSuccess (2 / 3 : ℝ) := by
  have hbound := Qatlib.Concepts.QueryComplexity.Reflections.twoReflectionQueryAlgorithm
  unfold Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionQueryAlgorithm at hbound
  obtain ⟨r, hr, C, E, hunit, hqc, hgate, hsucc⟩ :=
    hbound X n m hn input f v W hv hW
  let P : SourceProgram X := SourceProgram.mk n r input f C
    (Ket ((⟨0, hn⟩, false), ⟨0, hr⟩)) (fun x => if f x then E else Eᶜ)
  refine ⟨r, hr, P, hunit, hqc, hgate, ?_⟩
  intro x
  have hx : MeasureProb
        (Run (workspaceBitOracle (W := Fin r) (input x)) C
          (Ket ((⟨0, hn⟩, false), ⟨0, hr⟩))) (if f x then E else Eᶜ) ≥ (2 / 3 : ℝ) :=
    hsucc x
  exact hx

theorem thresholdGoal_complete (n m : ℕ) (hn : 0 < n)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ)
    (hv : SourceDualFeasible input f v W) (hW : 1 ≤ W) :
    (∃ (r : ℕ) (hr : 0 < r) (P : SourceProgram X),
        QueryCount P.circuit ≤ 1000000 * Nat.ceil W ∧
          P.DecidesWithSuccess (2 / 3 : ℝ)) ∧
      (∀ (r : ℕ) (M : List (SourceProgram X)) (P : SourceProgram X),
        P ∈ M → P.DecidesWithSuccess (2 / 3 : ℝ) →
          ∀ h : ∃ k, k ∈ sourceQueryCounts M (2 / 3 : ℝ),
            sourceMinQueries M (2 / 3 : ℝ) h ≤ QueryCount P.circuit) := by
  obtain ⟨r, hr, P, hunit, hqc, hgate, hD⟩ := clause85_complete n m hn input f v W hv hW
  refine ⟨⟨r, hr, P, hqc, hD⟩, ?_⟩
  intro r M P hP hD hne
  have hmem : QueryCount P.circuit ∈ sourceQueryCounts M (2 / 3 : ℝ) := by
    unfold sourceQueryCounts
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨hP, by simp [hD]⟩, rfl⟩
  exact finsetMinNat_le hmem

end Qatlib.Papers.ReflectQuery10.MainResults
