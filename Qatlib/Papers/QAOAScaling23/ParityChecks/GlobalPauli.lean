/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign

@[expose] public section

/-!
# Global Pauli parity checks

The two commutators for the QAOA checks in arXiv:2308.02342v2, Supplement §C,
measure two different binary coordinates of an error word. A word's total
Pauli weight alone does not determine either syndrome.
-/

set_option autoImplicit false

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank (booleanDot)
open scoped BigOperators

namespace Qatlib.Papers.QAOAScaling23.ParityChecks

/-- The global product of `X` checks, with no extra phase. -/
def globalX (n : ℕ) : PauliElem n := ⟨fun _ => .X, 0⟩

/-- The global product of `Z` checks, with no extra phase. -/
def globalZ (n : ℕ) : PauliElem n := ⟨fun _ => .Z, 0⟩

/-- Insert one Pauli letter on the selected wire and identities elsewhere. -/
def singlePauli {n : ℕ} (i : Fin n) (a : Pauli1) : PauliElem n :=
  ⟨fun j => if j = i then a else .I, 0⟩

/-- Count the letters (X,Y) that anticommute with a local (Z) check. -/
def xCount {n : ℕ} (w : PauliWord n) : ℕ :=
  (Finset.univ.filter (fun i => w i = .X ∨ w i = .Y)).card

/-- Count the letters (Y,Z) that anticommute with a local (X) check. -/
def zCount {n : ℕ} (w : PauliWord n) : ℕ :=
  (Finset.univ.filter (fun i => w i = .Y ∨ w i = .Z)).card

/-- Commutation with the matrix of the global X check means even Y/Z parity. -/
theorem commutes_globalX_iff {n : ℕ} (p : PauliElem n) :
    Commute (op p) (op (globalX n)) ↔ Even (zCount p.word) := by
  change op p * op (globalX n) = op (globalX n) * op p ↔ _
  rw [op_commute_iff_symplecticVec_form_zero]
  simp only [globalX, symplecticVec, symplecticForm, booleanDot, symplecticX, symplecticZ,
    reduceCtorEq, or_false, ite_true, ite_false, mul_zero, mul_one,
    Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_filter]
  simp [zCount, ZMod.natCast_eq_zero_iff_even]

/-- Commutation with the matrix of the global Z check means even X/Y parity. -/
theorem commutes_globalZ_iff {n : ℕ} (p : PauliElem n) :
    Commute (op p) (op (globalZ n)) ↔ Even (xCount p.word) := by
  change op p * op (globalZ n) = op (globalZ n) * op p ↔ _
  rw [op_commute_iff_symplecticVec_form_zero]
  simp only [globalZ, symplecticVec, symplecticForm, booleanDot, symplecticX, symplecticZ,
    reduceCtorEq, or_false, or_true, ite_true, ite_false, mul_zero, mul_one,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_filter]
  simp [xCount, ZMod.natCast_eq_zero_iff_even]

/-- A Pauli error changes a global check syndrome exactly when one of the two counts is odd. -/
theorem detected_iff {n : ℕ} (p : PauliElem n) :
    (¬ Commute (op p) (op (globalX n)) ∨ ¬ Commute (op p) (op (globalZ n))) ↔
      Odd (zCount p.word) ∨ Odd (xCount p.word) := by
  rw [commutes_globalX_iff, commutes_globalZ_iff, Nat.not_even_iff_odd, Nat.not_even_iff_odd]

/-- A predicate excluding the identity counts a single-wire insertion at most once. -/
private theorem count_single {n : ℕ} (i : Fin n) (a : Pauli1) (P : Pauli1 → Prop)
    [DecidablePred P] (hI : ¬P .I) :
    (Finset.univ.filter (fun j => P ((singlePauli i a).word j))).card =
      if P a then 1 else 0 := by
  by_cases h : P a
  · have he : Finset.univ.filter (fun j => P ((singlePauli i a).word j)) = {i} := by
      apply Finset.ext
      intro j
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hj : j = i <;> simp [singlePauli, hj, h, hI]
    simp [he, h]
  · have he : Finset.univ.filter (fun j => P ((singlePauli i a).word j)) = ∅ := by
      apply Finset.ext
      intro j
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      by_cases hj : j = i <;> simp [singlePauli, hj, h, hI]
    simp [he, h]

/-- Every nonidentity single-wire Pauli insertion is detected by at least one global check. -/
theorem single_qubit_pauli_detected {n : ℕ} (i : Fin n) (a : Pauli1) (ha : a ≠ .I) :
    ¬ Commute (op (singlePauli i a)) (op (globalX n)) ∨
      ¬ Commute (op (singlePauli i a)) (op (globalZ n)) := by
  rw [detected_iff, zCount, xCount,
    count_single i a (fun b => b = .Y ∨ b = .Z) (by decide),
    count_single i a (fun b => b = .X ∨ b = .Y) (by decide)]
  cases a
  · exact (ha rfl).elim
  all_goals decide

/-- The weight-three word XYZ commutes with both global checks. -/
theorem xyz_commutes_both :
    let p : PauliElem 3 := ⟨![.X, .Y, .Z], 0⟩
    (Finset.univ.filter (fun i => p.word i ≠ .I)).card = 3 ∧
      Commute (op p) (op (globalX 3)) ∧ Commute (op p) (op (globalZ 3)) := by
  dsimp only
  rw [commutes_globalX_iff, commutes_globalZ_iff]
  decide

/-- The odd-weight counterexample persists on an even register where both checks commute. -/
theorem xyzi_commutes_both :
    let p : PauliElem 4 := ⟨![.X, .Y, .Z, .I], 0⟩
    (Finset.univ.filter (fun i => p.word i ≠ .I)).card = 3 ∧
      Commute (op (globalX 4)) (op (globalZ 4)) ∧
      Commute (op p) (op (globalX 4)) ∧ Commute (op p) (op (globalZ 4)) := by
  dsimp only
  rw [commutes_globalZ_iff, commutes_globalX_iff, commutes_globalZ_iff]
  decide

end Qatlib.Papers.QAOAScaling23.ParityChecks
