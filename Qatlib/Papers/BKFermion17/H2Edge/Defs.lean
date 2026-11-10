/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BKFermion17.H2Edge
open Qatlib.Concepts.PauliClifford.PauliAlgebra

def h2B : Fin 4 → PauliElem 4
  | 0 => ⟨![Pauli1.Z, Pauli1.Z, Pauli1.I, Pauli1.I], 0⟩
  | 1 => ⟨![Pauli1.Z, Pauli1.I, Pauli1.Z, Pauli1.I], 0⟩
  | 2 => ⟨![Pauli1.I, Pauli1.I, Pauli1.Z, Pauli1.Z], 0⟩
  | 3 => ⟨![Pauli1.I, Pauli1.Z, Pauli1.I, Pauli1.Z], 0⟩

def isH2Edge : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 0, 3 => true
  | _, _ => false

def h2Edge (i j : Fin 4) : Prop := isH2Edge i j = true

instance h2EdgeDecidable (i j : Fin 4) : Decidable (h2Edge i j) := by
  unfold h2Edge
  infer_instance

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

def h2Loop : PauliElem 4 :=
  PauliElem.mul (PauliElem.mul (PauliElem.mul (h2A 0 1) (h2A 1 2)) (h2A 2 3)) (h2A 3 0)

end Qatlib.Papers.BKFermion17.H2Edge
