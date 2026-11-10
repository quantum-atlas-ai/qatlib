/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.H2Edge

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Papers.BKFermion17.H2Edge

instance pauliElemDecidableEq {n : ℕ} : DecidableEq (PauliElem n) := fun a b =>
  decidable_of_iff (a.word = b.word ∧ a.phase = b.phase) (by
    obtain ⟨wa, pa⟩ := a
    obtain ⟨wb, pb⟩ := b
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : wa = wb := h1
      have h2' : pa = pb := h2
      rw [h1', h2']
    · intro h
      exact ⟨congrArg PauliElem.word h, congrArg PauliElem.phase h⟩)

def pauliNeg {n : ℕ} (x : PauliElem n) : PauliElem n :=
  ⟨x.word, x.phase + 2⟩

def edgeCoincidence (i j k l : Fin 4) : ℕ :=
  (if i = k then 1 else 0) + (if i = l then 1 else 0) +
    (if j = k then 1 else 0) + (if j = l then 1 else 0)

def vertexCoincidence (i j k : Fin 4) : ℕ :=
  (if k = i then 1 else 0) + (if k = j then 1 else 0)

theorem h2B_sq (i : Fin 4) : PauliElem.mul (h2B i) (h2B i) = 1 := by
  decide +revert

theorem h2B_comm (i j : Fin 4) :
    PauliElem.mul (h2B i) (h2B j) = PauliElem.mul (h2B j) (h2B i) := by
  decide +revert

theorem h2A_sq (i j : Fin 4) (h : h2Edge i j) :
    PauliElem.mul (h2A i j) (h2A i j) = 1 := by
  decide +revert

theorem h2A_antisym (i j : Fin 4) (h : h2Edge i j) :
    h2A j i = pauliNeg (h2A i j) := by
  decide +revert

theorem h2A_mul_h2B (i j k : Fin 4) (h : h2Edge i j) :
    PauliElem.mul (h2A i j) (h2B k)
      = if vertexCoincidence i j k % 2 = 1
          then pauliNeg (PauliElem.mul (h2B k) (h2A i j))
          else PauliElem.mul (h2B k) (h2A i j) := by
  decide +revert

theorem h2A_mul_h2A (i j k l : Fin 4) (hij : h2Edge i j) (hkl : h2Edge k l) :
    PauliElem.mul (h2A i j) (h2A k l)
      = if edgeCoincidence i j k l % 2 = 1
          then pauliNeg (PauliElem.mul (h2A k l) (h2A i j))
          else PauliElem.mul (h2A k l) (h2A i j) := by
  decide +revert

theorem h2Loop_eq :
    h2Loop = ⟨![Pauli1.X, Pauli1.Y, Pauli1.Y, Pauli1.X], 2⟩ := by
  decide +revert

theorem h2Loop_ne_one : h2Loop ≠ 1 := by
  rw [h2Loop_eq]
  decide +revert

theorem h2Loop_sq : PauliElem.mul h2Loop h2Loop = 1 := by
  rw [h2Loop_eq]
  decide +revert

end Qatlib.Papers.BKFermion17.H2Edge
