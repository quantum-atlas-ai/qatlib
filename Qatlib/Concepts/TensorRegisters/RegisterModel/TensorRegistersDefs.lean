/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.BigOperators.Fin
import QuantumInfo.ForMathlib.Matrix

/-!
# Matrices and encodings for tensor registers

The construction `productMatrix` forms matrices on dependent products of finite labels.
`partitionReduce` and `partitionLift` express partial trace and local action through a register
partition, while `toReg`, `paddingFrame`, and `paddedGate` embed general finite registers into
binary registers. For background, see [NielsenChuang2010].

## Main statements

* `partitionReduce`: partial trace in partition coordinates.
* `paddingFrame`: basis embedding into a sufficiently large binary register.
* `paddedGate`: extension acting as the identity outside the encoded subspace.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open scoped BigOperators Kronecker

/-- The matrix on product labels whose entries are the products of the corresponding component
matrix entries. -/
noncomputable def productMatrix {ι : Type*} [Fintype ι] {S : ι → Type*} {T : ι → Type*}
    (A : ∀ i, Matrix (S i) (T i) ℂ) : Matrix (∀ i, S i) (∀ i, T i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- The retained-register matrix obtained by reindexing through `e` and taking the right partial
trace. -/
noncomputable def partitionReduce {S A B : Type*} [Fintype B] (e : S ≃ A × B)
    (X : Matrix S S ℂ) : Matrix A A ℂ := Matrix.traceRight (Matrix.reindex e e X)

/-- The full-register matrix obtained by transporting `U ⊗ₖ 1` back through the partition
equivalence `e`. -/
noncomputable def partitionLift {S A B : Type*} [DecidableEq B] (e : S ≃ A × B)
    (U : Matrix A A ℂ) : Matrix S S ℂ :=
  Matrix.reindex e.symm e.symm (U ⊗ₖ (1 : Matrix B B ℂ))

/-- Configurations of finite labels with component dimensions specified by `d`. -/
abbrev Labels {m : ℕ} (d : Fin m → ℕ) := ∀ i, Fin (d i)

/-- The equivalence between a label configuration and a finite index below the product of its
component dimensions. -/
def flatten {m : ℕ} (d : Fin m → ℕ) : Labels d ≃ Fin (∏ i, d i) := finPiFinEquiv

/-- The binary register encoding obtained by flattening a label configuration and embedding its
index below `2 ^ q`. -/
def toReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) ≤ 2 ^ q)
    (x : Labels d) : Reg q :=
  (bitVecEquiv q).symm (Fin.castLE h (flatten d x))

/-- The partial decoder returning the label configuration for an in-range binary value and
`none` otherwise. -/
def fromReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (b : Reg q) : Option (Labels d) :=
  if h : (bitVecEquiv q b).val < ∏ i, d i then
    some ((flatten d).symm ⟨(bitVecEquiv q b).val, h⟩)
  else none

/-- The label-to-binary-register equivalence when the product of label dimensions equals `2 ^
q`. -/
def exactRegEquiv {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) = 2 ^ q) :
    Labels d ≃ Reg q :=
  ((flatten d).trans (finCongr h)).trans (bitVecEquiv q).symm

/-- The basis embedding matrix with entry one at the binary encoding of each label and zero
elsewhere. -/
noncomputable def paddingFrame {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) : Matrix (Reg q) (Labels d) ℂ :=
  fun b x => if b = toReg d q h x then 1 else 0

/-- The extension of `U` through the padding frame, acting as the identity on the orthogonal
complement of the encoded subspace. -/
noncomputable def paddedGate {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ) :
    Matrix (Reg q) (Reg q) ℂ :=
  paddingFrame d q h * U * (paddingFrame d q h).conjTranspose +
    (1 - paddingFrame d q h * (paddingFrame d q h).conjTranspose)

end Qatlib.Concepts.TensorRegisters.RegisterModel
