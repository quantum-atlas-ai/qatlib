/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

/-!
# Pauli generators for the hydrogen graph

This module gives explicit four-qubit Pauli elements for the hydrogen graph. The vertex
generators `h2B` and oriented edge elements `h2A` determine the loop `h2Loop`; `h2Edge` records
the chosen ascending orientations of the four graph edges. See [SetiaWhitfield2018].

## Main statements

* `h2B`: the four vertex Pauli generators.
* `h2A`: the oriented edge Pauli elements.
* `h2Loop`: the product along the four-edge loop.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BKFermion17.H2Edge
open Qatlib.Concepts.PauliClifford.PauliAlgebra

/-- The four hydrogen vertex generators, each a phase-zero Pauli word with two `Z` factors. -/
def h2B : Fin 4 → PauliElem 4
  | 0 => ⟨![Pauli1.Z, Pauli1.Z, Pauli1.I, Pauli1.I], 0⟩
  | 1 => ⟨![Pauli1.Z, Pauli1.I, Pauli1.Z, Pauli1.I], 0⟩
  | 2 => ⟨![Pauli1.I, Pauli1.I, Pauli1.Z, Pauli1.Z], 0⟩
  | 3 => ⟨![Pauli1.I, Pauli1.Z, Pauli1.I, Pauli1.Z], 0⟩

/-- The Boolean test for the ascending hydrogen edges `(0, 1)`, `(1, 2)`, `(2, 3)`, and `(0,
3)`. -/
def isH2Edge : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 0, 3 => true
  | _, _ => false

/-- The ordered pair `(i, j)` is one of the four ascending hydrogen edges. -/
def h2Edge (i j : Fin 4) : Prop := isH2Edge i j = true

instance h2EdgeDecidable (i j : Fin 4) : Decidable (h2Edge i j) := by
  unfold h2Edge
  infer_instance

/-- The explicit hydrogen oriented edge Pauli elements, with reversed edges negated and all
other pairs assigned the identity. -/
def h2A : Fin 4 → Fin 4 → PauliElem 4
  | 0, 1 => ⟨![Pauli1.X, Pauli1.I, Pauli1.I, Pauli1.I], 0⟩
  | 1, 0 => ⟨![Pauli1.X, Pauli1.I, Pauli1.I, Pauli1.I], 2⟩
  | 1, 2 => ⟨![Pauli1.Z, Pauli1.I, Pauli1.X, Pauli1.I], 0⟩
  | 2, 1 => ⟨![Pauli1.Z, Pauli1.I, Pauli1.X, Pauli1.I], 2⟩
  | 2, 3 => ⟨![Pauli1.I, Pauli1.Z, Pauli1.Z, Pauli1.X], 0⟩
  | 3, 2 => ⟨![Pauli1.I, Pauli1.Z, Pauli1.Z, Pauli1.X], 2⟩
  | 0, 3 => ⟨![Pauli1.Z, Pauli1.X, Pauli1.I, Pauli1.I], 0⟩
  | 3, 0 => ⟨![Pauli1.Z, Pauli1.X, Pauli1.I, Pauli1.I], 2⟩
  | _, _ => ⟨![Pauli1.I, Pauli1.I, Pauli1.I, Pauli1.I], 0⟩

/-- The ordered product of hydrogen edge elements along the loop `0 → 1 → 2 → 3 → 0`. -/
def h2Loop : PauliElem 4 :=
  PauliElem.mul (PauliElem.mul (PauliElem.mul (h2A 0 1) (h2A 1 2)) (h2A 2 3)) (h2A 3 0)

end Qatlib.Papers.BKFermion17.H2Edge
