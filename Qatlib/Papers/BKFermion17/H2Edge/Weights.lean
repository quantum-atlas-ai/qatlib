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

def pauliWeight {n : ℕ} (w : Fin n → Pauli1) : ℕ :=
  (Finset.univ.filter (fun k => w k ≠ Pauli1.I)).card

def pauliElemWeight {n : ℕ} (x : PauliElem n) : ℕ :=
  pauliWeight x.word

def h2Degree : ℕ := 2

theorem h2B_weight_le (i : Fin 4) : pauliElemWeight (h2B i) ≤ h2Degree := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

theorem h2A_weight_le (i j : Fin 4) (_h : h2Edge i j) :
    pauliElemWeight (h2A i j) ≤ h2Degree + 1 := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

theorem h2A_weight_le_two_mul (i j : Fin 4) (h : h2Edge i j) :
    pauliElemWeight (h2A i j) ≤ 2 * h2Degree := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

end Qatlib.Papers.BKFermion17.H2Edge
