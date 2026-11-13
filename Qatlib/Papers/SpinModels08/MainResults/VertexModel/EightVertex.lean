/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.VertexModel.Basic

/-!
# Vertex support conditions and evaluator identities

This module specifies eight-vertex and six-vertex support patterns and the determinant relation
`FreeFermionCond`. It transfers a supplied partition-function evaluator to the associated
circuit matrix elements in the setting of [VanDenNestEtAl2009] and packages six-index weights as
three-site gates.

## Main statements

* `eightVertexGate_supported`: eight-vertex gates vanish between different parity sectors.
* `sixVertexGate_supported`: six-vertex gates also vanish on the two excluded equal-spin
  transitions.
* `eightVertex_evaluator_identity`: a supplied evaluator yields the corresponding circuit matrix
  elements.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.VertexModel

open Qatlib.Papers.SpinModels08.MainResults

/-- The eight-vertex support condition, requiring weights between different spin-parity sectors
to vanish. -/
def IsEightVertexShape (w : QWeight 2) : Prop :=
  w 0 0 0 1 = 0 ∧ w 0 0 1 0 = 0 ∧ w 0 1 0 0 = 0 ∧ w 0 1 1 1 = 0 ∧
  w 1 0 0 0 = 0 ∧ w 1 0 1 1 = 0 ∧ w 1 1 0 1 = 0 ∧ w 1 1 1 0 = 0

/-- The eight-vertex support condition together with vanishing `0011` and `1100` weights. -/
def IsSixVertexShape (w : QWeight 2) : Prop :=
  IsEightVertexShape w ∧ w 0 0 1 1 = 0 ∧ w 1 1 0 0 = 0

/-- The equality between the determinants of the even-parity and odd-parity two-by-two weight
blocks. -/
def FreeFermionCond (w : QWeight 2) : Prop :=
  w 0 0 0 0 * w 1 1 1 1 - w 0 0 1 1 * w 1 1 0 0 =
    w 0 1 0 1 * w 1 0 1 0 - w 0 1 1 0 * w 1 0 0 1

/-- An eight-vertex gate entry vanishes when the two spin pairs have different parity. -/
theorem eightVertexGate_supported (w : QWeight 2) (h : IsEightVertexShape w)
    (i j k l : Fin 2) (hpar : (i.val + j.val) % 2 ≠ (k.val + l.val) % 2) :
    twoLocalGate w (i, j) (k, l) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [twoLocalGate, IsEightVertexShape]

/-- A six-vertex gate entry vanishes across parity sectors and on the excluded `00` to `11` and
`11` to `00` transitions. -/
theorem sixVertexGate_supported (w : QWeight 2) (h : IsSixVertexShape w)
    (i j k l : Fin 2)
    (hbad : (i.val + j.val) % 2 ≠ (k.val + l.val) % 2 ∨ (i = 0 ∧ j = 0 ∧ k = 1 ∧ l = 1)
      ∨ (i = 1 ∧ j = 1 ∧ k = 0 ∧ l = 0)) :
    twoLocalGate w (i, j) (k, l) = 0 := by
  obtain ⟨h8, h0011, h1100⟩ := h
  rcases hbad with hpar | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact eightVertexGate_supported w h8 i j k l hpar
  · simpa [twoLocalGate] using h0011
  · simpa [twoLocalGate] using h1100

/-- An evaluator equal to the vertex-model partition contraction is also equal to the
corresponding circuit matrix element [VanDenNestEtAl2009]. -/
theorem evaluator_identity_transfer {q N : ℕ}
    (w : ∀ M : ℕ, Fin M → Fin N → QWeight q)
    (Zval : ∀ M : ℕ, Config q N → Config q N → ℂ)
    (hZ : ∀ (M : ℕ) (L R : Config q N), Zval M L R = vmPartition M (w M) L R) :
    ∀ (M : ℕ) (L R : Config q N), Zval M L R = matElem (vmCircuit M (w M)) L R := by
  intro M L R
  rw [hZ M L R, matElem_eq_apply, vmPartition_eq_vmCircuit]

/-- For weights satisfying the eight-vertex and free-fermion conditions, a supplied partition
evaluator equals the circuit matrix element [VanDenNestEtAl2009]. -/
theorem eightVertex_evaluator_identity {N : ℕ}
    (w : ∀ M : ℕ, Fin M → Fin N → QWeight 2)
    (_hshape : ∀ (M : ℕ) (c : Fin M) (r : Fin N), IsEightVertexShape (w M c r))
    (_hff : ∀ (M : ℕ) (c : Fin M) (r : Fin N), FreeFermionCond (w M c r))
    (Zval : ∀ M : ℕ, Config 2 N → Config 2 N → ℂ)
    (hZ : ∀ (M : ℕ) (L R : Config 2 N), Zval M L R = vmPartition M (w M) L R) :
    ∀ (M : ℕ) (L R : Config 2 N), Zval M L R = matElem (vmCircuit M (w M)) L R :=
  evaluator_identity_transfer w Zval hZ

/-- The three-site matrix obtained by grouping a six-index weight into two triples. -/
def threeLocalGate {q : ℕ} (w6 : Fin q → Fin q → Fin q → Fin q → Fin q → Fin q → ℂ) :
    Matrix (Fin q × Fin q × Fin q) (Fin q × Fin q × Fin q) ℂ :=
  fun (i, j, k) (l, m, n) => w6 i j k l m n

/-- The entries of a three-site gate are its six-index weights. -/
theorem threeLocalGate_apply {q : ℕ} (w6 : Fin q → Fin q → Fin q → Fin q → Fin q → Fin q → ℂ)
    (i j k l m n : Fin q) :
    threeLocalGate w6 (i, j, k) (l, m, n) = w6 i j k l m n := rfl

end Qatlib.Papers.SpinModels08.MainResults.VertexModel
