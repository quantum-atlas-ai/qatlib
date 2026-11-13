/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.Defs

/-!
# Pauli weights of hydrogen edge generators

This module counts nonidentity factors in Pauli words and bounds the weights of the explicit
hydrogen generators. Vertex weights are at most the graph degree, while edge weights are bounded
by both the degree plus one and twice the degree. See [SetiaWhitfield2018].

## Main statements

* `h2B_weight_le`: vertex weight is at most the hydrogen degree.
* `h2A_weight_le`: edge weight is at most the degree plus one.
* `h2A_weight_le_two_mul`: edge weight is at most twice the degree.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BKFermion17.H2Edge
open Qatlib.Concepts.PauliClifford.PauliAlgebra

/-- The number of nonidentity factors in a Pauli word. -/
def pauliWeight {n : ℕ} (w : Fin n → Pauli1) : ℕ :=
  (Finset.univ.filter (fun k => w k ≠ Pauli1.I)).card

/-- The weight of the word underlying a Pauli element, ignoring its phase. -/
def pauliElemWeight {n : ℕ} (x : PauliElem n) : ℕ :=
  pauliWeight x.word

/-- The hydrogen graph degree, equal to two. -/
def h2Degree : ℕ := 2

/-- Each hydrogen vertex generator has Pauli weight at most the hydrogen graph degree. -/
theorem h2B_weight_le (i : Fin 4) : pauliElemWeight (h2B i) ≤ h2Degree := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

/-- Each hydrogen edge generator has Pauli weight at most the graph degree plus one. -/
theorem h2A_weight_le (i j : Fin 4) (_h : h2Edge i j) :
    pauliElemWeight (h2A i j) ≤ h2Degree + 1 := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

/-- Each hydrogen edge generator has Pauli weight at most twice the graph degree. -/
theorem h2A_weight_le_two_mul (i j : Fin 4) (h : h2Edge i j) :
    pauliElemWeight (h2A i j) ≤ 2 * h2Degree := by
  unfold pauliElemWeight pauliWeight h2Degree
  decide +revert

end Qatlib.Papers.BKFermion17.H2Edge
