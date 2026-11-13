/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable

/-!
# Preparing an evaluated table by oracle queries

This module builds an explicit unitary query circuit for loading function values into table
records. The construction `fetchRow` swaps one row into the query registers, evaluates the
oracle, and swaps it back, providing the initialization stage for
[BrassardHoyerTapp1998Collision].

The theorem `prepare_table` proves that all `k` rows are loaded with exactly `k` queries. The
input enumeration and stored value set are related to a chosen finite input table.

## Main statements

* `fetchRow_run`: On a basis state, `fetchRow j` adds `F` of the stored input to row `j`'s value
  and preserves the active registers.
* `prepare_table`: The full table-building circuit is unitary, uses exactly `k` queries, and
  loads all `k` function values while preserving the active pair
  [BrassardHoyerTapp1998Collision].
* `loaded_values`: The values stored by loading the enumeration of `K` form exactly the finite
  set `K.image F`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

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

/-- Swaps the active input-value pair with the table row at index `j`. -/
def swapRow {k : ℕ} (j : Fin k) (p : (X × R) × Memory (X := X) (R := R) k) :
    (X × R) × Memory (X := X) (R := R) k :=
  (p.2 j, Function.update p.2 j p.1)

omit [AddCommGroup R] [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] in

/-- Swapping the active pair with a fixed table row is an involution. -/
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

/-- The permutation matrix exchanging the active input-value pair with table row `j`. -/
def swapGate {k : ℕ} (j : Fin k) :
    Matrix ((X × R) × Memory (X := X) (R := R) k) ((X × R) × Memory (X := X) (R := R) k) ℂ :=
  permMatrix (swapRow j)

omit [AddCommGroup R] in

/-- The row-swap gate is unitary. -/
theorem swapGate_unitary {k : ℕ} (j : Fin k) :
    swapGate (X := X) (R := R) j ∈ Matrix.unitaryGroup ((X × R) × Memory (X := X) (R := R) k) ℂ :=
  permMatrix_unitary (swapRow_involutive j)

/-- The circuit swapping row `j` into the active registers, applying one oracle query, and
swapping it back. -/
def fetchRow {k : ℕ} (j : Fin k) : Circuit ((X × R) × Memory (X := X) (R := R) k) :=
  [.gate (swapGate j), .query, .gate (swapGate j)]

/-- On a basis state, `fetchRow j` adds `F` of the stored input to row `j`'s value and preserves
the active registers. -/
theorem fetchRow_run (F : X → R) {k : ℕ} (j : Fin k) (q : X × R) (L : Memory (X := X) (R := R) k) :
    Run (oracle F k) (fetchRow j) (Qatlib.Foundations.PureStateMath.Ket (q, L)) =
      Qatlib.Foundations.PureStateMath.Ket
        (q, Function.update L j ((L j).1, (L j).2 + F (L j).1)) := by
  simp only [fetchRow, Run, swapGate, applyGate_permMatrix_ket (swapRow_involutive j)]
  simp [swapRow, oracle_ket, applyGate_permMatrix_ket (swapRow_involutive j)]

/-- The circuit obtained by concatenating row-fetch circuits for the indices in `js`. -/
def buildWord {k : ℕ} (js : List (Fin k)) : Circuit ((X × R) × Memory (X := X) (R := R) k) :=
  js.flatMap fetchRow

/-- The table update obtained by adding the function value at each row index in the list,
counting repeated visits. -/
def fill (F : X → R) {k : ℕ} : List (Fin k) → Memory (X := X) (R := R) k → Memory (X := X) (R := R) k
  | [], L => L
  | j :: js, L => fill F js (Function.update L j ((L j).1, (L j).2 + F (L j).1))

/-- Executing `buildWord js` on a basis state performs the table update `fill F js` and
preserves the active pair. -/
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

/-- At row `i`, filling adds `F` of its input as many times as `i` occurs in `js`. -/
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

/-- The table whose row `j` is the accurate record `(xs j, F (xs j))`. -/
def loaded {k : ℕ} (F : X → R) (xs : Fin k → X) : Memory (X := X) (R := R) k :=
  fun j => (xs j, F (xs j))

omit [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] in

/-- Visiting every row once transforms a table of inputs with zero values into `loaded F xs`. -/
theorem fill_all (F : X → R) {k : ℕ} (xs : Fin k → X) :
    fill F (List.finRange k) (fun j => (xs j, 0)) = loaded F xs := by
  funext i
  rw [fill_apply]
  have hc : (List.finRange k).count i = 1 := by simp
  simp [hc, loaded]

omit [AddCommGroup R] in

/-- A row-fetch circuit is unitary and uses exactly one oracle query. -/
theorem fetchRow_resources {k : ℕ} (j : Fin k) :
    QueryCount (fetchRow (X := X) (R := R) j) = 1 ∧ IsUnitaryCircuit (fetchRow (X := X) (R := R) j) := by
  constructor
  · rfl
  · simp [fetchRow, swapGate_unitary]

omit [AddCommGroup R] in

/-- The table-building circuit is unitary and uses exactly `js.length` oracle queries. -/
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

/-- The full table-building circuit is unitary, uses exactly `k` queries, and loads all `k`
function values while preserving the active pair [BrassardHoyerTapp1998Collision]. -/
theorem prepare_table (F : X → R) {k : ℕ} (xs : Fin k → X) (q : X × R) :
    QueryCount (buildWord (X := X) (R := R) (List.finRange k)) = k ∧
    IsUnitaryCircuit (buildWord (X := X) (R := R) (List.finRange k)) ∧
    Run (oracle F k) (buildWord (List.finRange k))
      (Qatlib.Foundations.PureStateMath.Ket (q, fun j => (xs j, 0))) =
      Qatlib.Foundations.PureStateMath.Ket (q, loaded F xs) := by
  have hc := buildWord_resources (X := X) (R := R) (List.finRange k)
  refine ⟨by simpa using hc.1, hc.2, ?_⟩
  rw [buildWord_run, fill_all]

/-- An enumeration of the elements of `K` indexed by `Fin (Fintype.card K)`. -/
def inputs (K : Finset X) : Fin (Fintype.card K) → X :=
  fun j => ((Fintype.equivFin K).symm j).val

omit [Fintype X] [AddCommGroup R] [Fintype R] [DecidableEq R] in

/-- The image of the chosen input enumeration is exactly `K`. -/
theorem inputs_image (K : Finset X) : Finset.univ.image (inputs K) = K := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Fintype.equivFin K).symm j).property
  · intro hx
    exact ⟨Fintype.equivFin K ⟨x, hx⟩, by simp [inputs]⟩

omit [Fintype X] [AddCommGroup R] [Fintype R] in

/-- The values stored by loading the enumeration of `K` form exactly the finite set `K.image F`. -/
theorem loaded_values (F : X → R) (K : Finset X) : values (loaded F (inputs K)) = K.image F := by
  change Finset.univ.image (fun j => F (inputs K j)) = K.image F
  have h := congrArg (fun S : Finset X => S.image F) (inputs_image K)
  simpa only [Finset.image_image, Function.comp_def] using h

end Qatlib.Papers.CollisionProb97.MainResults.TablePreparation
