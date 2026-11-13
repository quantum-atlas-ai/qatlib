/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.MatrixTensor
import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Basic gate vocabulary

This module defines Boolean-indexed Pauli and S gates, their scalar multiplication table, and
the algebra equivalence transporting them to `Fin 2`. It also fixes the one-qubit register
equivalence and the matrix conventions for SWAP and Toffoli.

These definitions supply a shared gate vocabulary for the standard circuit identities described
in [NielsenChuang2010].

## Main statements

* `pauliBool`: labels the identity and X, Y, Z by `Fin 4`.
* `pauliProductIndex`: computes the Pauli label of a product.
* `pauliProductPhase`: computes the corresponding scalar phase.
* `toffoliGate`: defines the matrix of the controlled-controlled bit update.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GateVocabulary.GateVocab

open Matrix

/-- The Boolean-indexed Pauli Y matrix, with off-diagonal entries `-i` and `i`. -/
def pauliYBool : Matrix Bool Bool ℂ :=
  fun i j => if i = j then 0 else if i then Complex.I else -Complex.I

/-- The Boolean-indexed phase gate S with diagonal entries 1 and `i`. -/
def phaseS : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then Complex.I else 1)

/-- The Boolean-indexed Pauli family, assigning labels 0, 1, 2, and 3 to the identity, X, Y, and
Z. -/
def pauliBool (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a.val = 0 then 1 else if a.val = 1 then Qatlib.Foundations.PureStateMath.PauliX else
    if a.val = 2 then pauliYBool else Qatlib.Foundations.PureStateMath.PauliZ

/-- The Pauli label of a product, computed by componentwise addition modulo two of the binary
label bits. -/
def pauliProductIndex (a b : Fin 4) : Fin 4 :=
  ⟨(a.val % 2 + b.val % 2) % 2 + 2 * ((a.val / 2 + b.val / 2) % 2),
    by fin_cases a <;> fin_cases b <;> decide⟩

/-- The equivalence between a one-qubit register configuration and its unique Boolean
coordinate. -/
def regOneBool : Qatlib.Foundations.PureStateMath.Reg 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool

/-- The scalar phase in the product of two Pauli matrices: 1 for identity factors or equal
labels, `i` for cyclic distinct nonidentity labels, and `-i` otherwise. -/
def pauliProductPhase (a b : Fin 4) : ℂ :=
  if a.val = 0 ∨ b.val = 0 ∨ a.val = b.val then 1 else
    if (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 3) ∨
      (a.val = 3 ∧ b.val = 1) then Complex.I else -Complex.I

/-- The complex algebra equivalence reindexing Boolean gate matrices along `boolEquivFin2`. -/
def toFinGate : Matrix Bool Bool ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ Qatlib.Foundations.PureStateMath.boolEquivFin2

/-- The Pauli family transported from Boolean indices to `Fin 2` indices. -/
def pauliFin (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := toFinGate (pauliBool a)
/-- The three nonidentity Pauli matrices indexed by `Fin 3` in X, Y, Z order. -/
def pauliAxis (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliFin ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩
/-- The Hadamard gate transported from Boolean indices to `Fin 2` indices. -/
def hadamardFin : Matrix (Fin 2) (Fin 2) ℂ :=
    toFinGate Qatlib.Foundations.PureStateMath.Hadamard
/-- The phase gate S transported from Boolean indices to `Fin 2` indices. -/
def phaseSFin : Matrix (Fin 2) (Fin 2) ℂ := toFinGate phaseS

/-- The permutation matrix exchanging the two Boolean tensor factors. -/
def swapGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  permMatrix (fun x => (x.2, x.1))

/-- The basis update that XORs the conjunction of the two control bits into the target bit. -/
def toffoliUpdate {n : ℕ} (a b t : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.PureStateMath.Reg n :=
  Function.update x t (x t ^^ (x a && x b))

/-- The matrix associated with the Toffoli basis update on the specified control and target
wires. -/
def toffoliGate {n : ℕ} (a b t : Fin n) : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  permMatrix (toffoliUpdate a b t)

end Qatlib.Concepts.GateVocabulary.GateVocab
