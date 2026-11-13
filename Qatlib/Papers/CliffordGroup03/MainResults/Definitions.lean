/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

/-!
# Binary Pauli and Clifford coordinates

This module introduces the binary vectors, bilinear-form matrices, extended coordinates, and
phase conventions used in [DehaeneDeMoor2003]. The matrices `tau1` and `tau` encode Pauli
operators, while `RepresentsClifford` records their generator conjugation equations.

## Main statements

* `Umat`, `Pmat`, and `Symplectic`: the binary form and its preservation condition.
* `CbarMat`, `Ubar`, and `lowsOpt`: extended matrices for phase formulas.
* `RepresentsClifford`: the binary data specified by generator conjugation.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

namespace Qatlib.Papers.CliffordGroup03.MainResults

/-- The type of binary vectors of length `n`. -/
abbrev BV (n : ℕ) := BooleanVec n

/-- The binary block matrix with an identity block in the upper right and zeros elsewhere. -/
def Umat (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  fun i j => if i.val < n ∧ j.val = i.val + n then 1 else 0

/-- The binary symplectic-form matrix `Umat n + (Umat n)ᵀ`. -/
def Pmat (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) := Umat n + (Umat n)ᵀ

/-- The condition `Cᵀ * Pmat n * C = Pmat n` expressing preservation of the binary symplectic
form. -/
def Symplectic (n : ℕ) (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) : Prop :=
  Cᵀ * Pmat n * C = Pmat n

/-- The strict lower-triangular part of a binary matrix. -/
def lows {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => if j.val < i.val then M i j else 0

/-- The vector of diagonal entries of a binary matrix. -/
def diagVec {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : BV m := fun i => M i i

/-- The condition that a binary matrix equals its transpose. -/
def Symm {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Prop := Mᵀ = M

/-- The binary quadratic expression given by the double sum of `x i * M i j * x j`. -/
def quadForm {ι : Type*} [Fintype ι] (M : Matrix ι ι (ZMod 2)) (x : ι → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, x i * M i j * x j

/-- The binary standard basis vector supported at `k`. -/
def stdBasis {m : ℕ} (k : Fin m) : BV m := fun i => if i = k then 1 else 0

/-- Splits a binary vector of length `2*n` into its first and last `n` coordinates. -/
def splitVec {n : ℕ} (a : BV (2 * n)) : BV n × BV n :=
  (fun j => a ⟨j.val, by have := j.isLt; omega⟩,
   fun j => a ⟨n + j.val, by have := j.isLt; omega⟩)

/-- The `k`-th column of a binary matrix, viewed as a vector. -/
def colVec {m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod 2)) (k : Fin m) : BV m := fun i => C i k

/-- The Pauli letter determined by two binary coordinates, with `(0,0)`, `(1,0)`, `(0,1)`, and
`(1,1)` giving `I`, `Z`, `X`, and `Y` respectively. -/
def letter (v w : ZMod 2) : Pauli1 :=
  if v = 1 then (if w = 1 then .Y else .Z) else (if w = 1 then .X else .I)

/-- The single-qubit matrix `i^(v*w) • P1 (letter v w)` used in the binary Pauli convention. -/
def tau1 (v w : ZMod 2) : Matrix Bool Bool ℂ :=
  (Complex.I ^ (v * w).val : ℂ) • P1 (letter v w)

/-- The tensor product of the single-qubit matrices `tau1` specified by a pair of binary
vectors. -/
def tau {n : ℕ} (a : BV n × BV n) : Matrix (Reg n) (Reg n) ℂ :=
  productMatrix (fun k => tau1 (a.1 k) (a.2 k))

/-- The binary-coordinate index type extended by one distinguished coordinate `none`. -/
abbrev Ext (n : ℕ) := Option (Fin (2 * n))

/-- Extends the binary vector `b` by the phase bit `δ` at the distinguished coordinate. -/
def evec {n : ℕ} (b : BV (2 * n)) (δ : ZMod 2) : Ext n → ZMod 2
  | some i => b i
  | none => δ

/-- The extended binary matrix with blocks `C`, zero, the row `d`, and a final diagonal entry
one. -/
def CbarMat {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (d : BV (2 * n)) :
    Matrix (Ext n) (Ext n) (ZMod 2)
  | some i, some j => C i j
  | some _, none => 0
  | none, some j => d j
  | none, none => 1

/-- Extends `Umat n` by a final diagonal entry one and zero off-diagonal entries involving the
distinguished coordinate. -/
def Ubar (n : ℕ) : Matrix (Ext n) (Ext n) (ZMod 2)
  | some i, some j => Umat n i j
  | some _, none => 0
  | none, some _ => 0
  | none, none => 1

/-- Extends the binary vector `h` by zero at the distinguished coordinate. -/
def hbar {n : ℕ} (h : BV (2 * n)) : Ext n → ZMod 2
  | some i => h i
  | none => 0

/-- The strict lower-triangular part of an extended binary matrix, treating the distinguished
coordinate as the last index. -/
def lowsOpt {n : ℕ} (M : Matrix (Ext n) (Ext n) (ZMod 2)) : Matrix (Ext n) (Ext n) (ZMod 2) :=
  fun i j =>
    match i, j with
    | none, some _ => M i j
    | none, none => 0
    | some i', some j' => if j'.val < i'.val then M i j else 0
    | some _, none => 0

/-- The binary dot product on the extended coordinate type. -/
def extDot {n : ℕ} (x y : Ext n → ZMod 2) : ZMod 2 := ∑ o, x o * y o

/-- The diagonal vector of a matrix on the extended coordinate type. -/
def diagVecOpt {n : ℕ} (M : Matrix (Ext n) (Ext n) (ZMod 2)) : Ext n → ZMod 2 := fun i => M i i

/-- The generator conjugation equations specifying the binary matrix `C` and sign vector `h`
associated with `Q`. The phase factors use the diagonal of `Cᵀ * Umat n * C`. -/
def RepresentsClifford {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ)
    (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h : BV (2 * n)) : Prop :=
  ∀ k : Fin (2 * n),
    Q * tau (splitVec (stdBasis k)) * Qᴴ =
      ((Complex.I ^ ((diagVec (Cᵀ * Umat n * C)) k).val : ℂ) *
          ((-1 : ℂ) ^ (h k).val)) • tau (splitVec (colVec C k))

end Qatlib.Papers.CliffordGroup03.MainResults
