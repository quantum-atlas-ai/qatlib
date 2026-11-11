/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDimension

/-!
# Canonical zero-state stabilizer generators

This module verifies consistency and independence of the canonical `zeroTableau`. Its symplectic
rows are the standard basis vectors in the Z coordinates, making it the starting tableau for
Clifford state preparation; see [DehaeneDeMoor2003] for the binary stabilizer framework.

## Main statements

* `zero_row_symp`: Zero-tableau rows have standard basis Z coordinates.
* `zero_tableau_consistent`: The canonical zero tableau is consistent.
* `zero_tableau_independent`: Its decoded Pauli generators are independent.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PauliClifford.ExactRank

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)
open scoped Classical

/-- The ith zero-tableau row has zero X coordinate and the ith standard basis vector as its Z
coordinate. -/
theorem zero_row_symp (n : ℕ) (i : Fin n) :
    rowSympVec (zeroTableau n) i = (0,Pi.single i (1 : ZMod 2)) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i <;>
      simp [rowSympVec,symplecticVec,zeroTableau,Row.decode,letter,symplecticX,h]
  · funext j
    by_cases h : j=i <;>
      simp [rowSympVec,symplecticVec,zeroTableau,Row.decode,letter,symplecticZ,Pi.single_apply,h]

/-- The zero tableau is consistent. -/
theorem zero_tableau_consistent (n : ℕ) : ConsistentTableau (zeroTableau n) := by
  constructor
  · intro i
    exact Or.inl rfl
  · intro i j
    apply (op_commute_iff_symplecticVec_form_zero _ _).mpr
    change symplecticForm (rowSympVec (zeroTableau n) i) (rowSympVec (zeroTableau n) j) = 0
    rw [zero_row_symp,zero_row_symp]
    simp [symplecticForm,booleanDot]

/-- The symplectic vectors of the zero-tableau rows are linearly independent over the
two-element field. -/
theorem zero_tableau_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 2) (rowSympVec (zeroTableau n)) := by
  have h := (Pi.basisFun (ZMod 2) (Fin n)).linearIndependent.map'
    (LinearMap.inr (ZMod 2) (BooleanVec n) (BooleanVec n))
    (LinearMap.ker_eq_bot.mpr LinearMap.inr_injective)
  convert! h using 1
  funext i
  rw [zero_row_symp]
  simp

/-- The decoded generators of the zero tableau are independent. -/
theorem zero_tableau_independent (n : ℕ) :
    IndependentGenerators (tableauGenerators (zeroTableau n)) :=
  independent_of_row_linearIndependent _ (zero_tableau_linearIndependent n)

end Qatlib.Concepts.PauliClifford.PauliAlgebra
