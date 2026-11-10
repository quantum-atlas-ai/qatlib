/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Papers.CollisionProb97.MainResults.TablePreparation
open ReadOnlyTable
variable {X R : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

def swapRow {k : ℕ} (j : Fin k) (p : (X × R) × Memory (X := X) (R := R) k) :
    (X × R) × Memory (X := X) (R := R) k :=
  (p.2 j, Function.update p.2 j p.1)

omit [AddCommGroup R] [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] in

theorem swapRow_involutive {k : ℕ} (j : Fin k) : Function.Involutive (swapRow (X := X) (R := R) j) := by
  intro p
  rcases p with ⟨q, L⟩
  simp only [swapRow, Function.update_self]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · simp [Function.update_of_ne hi]

def swapGate {k : ℕ} (j : Fin k) :
    Matrix ((X × R) × Memory (X := X) (R := R) k) ((X × R) × Memory (X := X) (R := R) k) ℂ :=
  permMatrix (swapRow j)

omit [AddCommGroup R] in

theorem swapGate_unitary {k : ℕ} (j : Fin k) :
    swapGate (X := X) (R := R) j ∈ Matrix.unitaryGroup ((X × R) × Memory (X := X) (R := R) k) ℂ :=
  permMatrix_unitary (swapRow_involutive j)

def fetchRow {k : ℕ} (j : Fin k) : Circuit ((X × R) × Memory (X := X) (R := R) k) :=
  [.gate (swapGate j), .query, .gate (swapGate j)]

theorem fetchRow_run (F : X → R) {k : ℕ} (j : Fin k) (q : X × R) (L : Memory (X := X) (R := R) k) :
    Run (oracle F k) (fetchRow j) (Qatlib.Foundations.PureStateMath.Ket (q, L)) =
      Qatlib.Foundations.PureStateMath.Ket
        (q, Function.update L j ((L j).1, (L j).2 + F (L j).1)) := by
  simp only [fetchRow, Run, swapGate, applyGate_permMatrix_ket (swapRow_involutive j)]
  simp [swapRow, oracle_ket, applyGate_permMatrix_ket (swapRow_involutive j)]

def buildWord {k : ℕ} (js : List (Fin k)) : Circuit ((X × R) × Memory (X := X) (R := R) k) :=
  js.flatMap fetchRow

def fill (F : X → R) {k : ℕ} : List (Fin k) → Memory (X := X) (R := R) k → Memory (X := X) (R := R) k
  | [], L => L
  | j :: js, L => fill F js (Function.update L j ((L j).1, (L j).2 + F (L j).1))

theorem buildWord_run (F : X → R) {k : ℕ} (js : List (Fin k)) (q : X × R) (L : Memory (X := X) (R := R) k) :
    Run (oracle F k) (buildWord js) (Qatlib.Foundations.PureStateMath.Ket (q, L)) =
      Qatlib.Foundations.PureStateMath.Ket (q, fill F js L) := by
  induction js generalizing L with
  | nil => rfl
  | cons j js ih =>
    rw [buildWord, List.flatMap_cons, run_append]
    rw [fetchRow_run]
    exact ih _

omit [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] in

theorem fill_apply (F : X → R) {k : ℕ} (js : List (Fin k)) (L : Memory (X := X) (R := R) k) (i : Fin k) :
    fill F js L i = ((L i).1, (L i).2 + js.count i • F (L i).1) := by
  induction js generalizing L with
  | nil => simp [fill]
  | cons j js ih =>
    rw [fill, ih]
    by_cases hi : i = j
    · subst i
      simp [add_nsmul, add_assoc, add_comm]
    · simp [hi, Ne.symm hi]

def loaded {k : ℕ} (F : X → R) (xs : Fin k → X) : Memory (X := X) (R := R) k :=
  fun j => (xs j, F (xs j))

omit [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] in

theorem fill_all (F : X → R) {k : ℕ} (xs : Fin k → X) :
    fill F (List.finRange k) (fun j => (xs j, 0)) = loaded F xs := by
  funext i
  rw [fill_apply]
  have hc : (List.finRange k).count i = 1 := by simp
  simp [hc, loaded]

omit [AddCommGroup R] in

theorem fetchRow_resources {k : ℕ} (j : Fin k) :
    QueryCount (fetchRow (X := X) (R := R) j) = 1 ∧ IsUnitaryCircuit (fetchRow (X := X) (R := R) j) := by
  constructor
  · rfl
  · simp [fetchRow, swapGate_unitary]

omit [AddCommGroup R] in

theorem buildWord_resources {k : ℕ} (js : List (Fin k)) :
    QueryCount (buildWord (X := X) (R := R) js) = js.length ∧ IsUnitaryCircuit (buildWord (X := X) (R := R) js) := by
  induction js with
  | nil => exact ⟨rfl, isUnitaryCircuit_nil⟩
  | cons j js ih =>
    constructor
    · change QueryCount (fetchRow j ++ buildWord js) = js.length + 1
      rw [queryCount_append, (fetchRow_resources j).1, ih.1]
      omega
    · change IsUnitaryCircuit (fetchRow j ++ buildWord js)
      exact (isUnitaryCircuit_append _ _).mpr ⟨(fetchRow_resources j).2, ih.2⟩

theorem prepare_table (F : X → R) {k : ℕ} (xs : Fin k → X) (q : X × R) :
    QueryCount (buildWord (X := X) (R := R) (List.finRange k)) = k ∧
    IsUnitaryCircuit (buildWord (X := X) (R := R) (List.finRange k)) ∧
    Run (oracle F k) (buildWord (List.finRange k))
      (Qatlib.Foundations.PureStateMath.Ket (q, fun j => (xs j, 0))) =
      Qatlib.Foundations.PureStateMath.Ket (q, loaded F xs) := by
  have hc := buildWord_resources (X := X) (R := R) (List.finRange k)
  refine ⟨by simpa using hc.1, hc.2, ?_⟩
  rw [buildWord_run, fill_all]

def inputs (K : Finset X) : Fin (Fintype.card K) → X :=
  fun j => ((Fintype.equivFin K).symm j).val

omit [Fintype X] [AddCommGroup R] [Fintype R] [DecidableEq R] in

theorem inputs_image (K : Finset X) : Finset.univ.image (inputs K) = K := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Fintype.equivFin K).symm j).property
  · intro hx
    exact ⟨Fintype.equivFin K ⟨x, hx⟩, by simp [inputs]⟩

omit [Fintype X] [AddCommGroup R] [Fintype R] in

theorem loaded_values (F : X → R) (K : Finset X) : values (loaded F (inputs K)) = K.image F := by
  change Finset.univ.image (fun j => F (inputs K j)) = K.image F
  have h := congrArg (fun S : Finset X => S.image F) (inputs_image K)
  simpa only [Finset.image_image, Function.comp_def] using h

end Qatlib.Papers.CollisionProb97.MainResults.TablePreparation
