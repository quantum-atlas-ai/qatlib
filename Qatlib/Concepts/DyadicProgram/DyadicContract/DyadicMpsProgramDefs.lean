/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Log
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Gaussian integer programs for dyadic contractions

This module represents Gaussian integers by `GI` and defines dyadic decoding into the complex
numbers. `dot`, `row`, and `run` implement matrix-chain contraction from the zero-indexed
standard basis row, and `scalar` selects the zero right boundary. These operations realize the
matrix products underlying MPS contractions discussed in [Schollwock2011].

`Counted` and the corresponding counted programs attach integer multiplication and addition
counts to the same row recursion. `matrixWord` gives the complex matrix product obtained by
decoding the input matrices.

## Main statements

* `decode`: dyadic interpretation of integer pairs.
* `scalar`: contraction with both boundary indices zero.
* `runCounted`: matrix-chain contraction with arithmetic counters.
* `matrixWord`: the decoded complex matrix product.

## References

* [Schollwöck, 2011][Schollwock2011]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.DyadicProgram.DyadicContract
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Integer pairs representing the real and imaginary components of Gaussian integers. -/
abbrev GI := ℤ×ℤ
/-- Componentwise addition of Gaussian integer pairs. -/
def add (x y : GI) : GI := (x.1+y.1,x.2+y.2)
/-- Multiplication of Gaussian integer pairs using the real and imaginary component formulas. -/
def mul (x y : GI) : GI := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1)
/-- Interpret a Gaussian integer pair as a complex number divided by `2 ^ p`. -/
noncomputable def decode (p : ℕ) (z : GI) : ℂ := ((z.1:ℂ)+(z.2:ℂ)*Complex.I)/(2:ℂ)^p

/-- A component of a Gaussian integer row-matrix product, computed by a left-folded sum. -/
def dot {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) : GI :=
  (List.ofFn (fun i : Fin D => mul (v i) (A i j))).foldl add (0,0)
/-- Multiply a Gaussian integer row vector by a square matrix. -/
def row {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) : Fin D→GI := fun j=>dot v A j

/-- The Gaussian integer row vector equal to one at index zero and zero elsewhere. -/
def initial (D : ℕ) : Fin D→GI := fun i=>if i.val=0 then (1,0) else (0,0)
/-- Apply the matrices in list order to the initial Gaussian integer row vector. -/
def run {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : Fin D→GI := As.foldl row (initial D)

/-- The zero-indexed output component of `run As`, with a positive bond dimension. -/
def scalar {D : ℕ} (hD : 0 < D) (As : List (Matrix (Fin D) (Fin D) GI)) : GI := run As ⟨0,hD⟩
/-- The ordered product of matrices decoded entrywise at dyadic precision `p`. -/
noncomputable def matrixWord {D : ℕ} (p : ℕ) (As : List (Matrix (Fin D) (Fin D) GI)) : Matrix (Fin D) (Fin D) ℂ :=
  (As.map fun A=>fun i j=>decode p (A i j)).prod

/-- A value paired with counts of integer multiplications and additions. -/
structure Counted (α : Type) where
 value : α
 muls : ℕ
 adds : ℕ

/-- A Gaussian integer dot product recording four integer multiplications and four additions per
summand. -/
def dotCounted {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) (j : Fin D) : Counted GI :=
  (List.ofFn (fun i : Fin D=>(v i,A i j))).foldl
    (fun s xy=>⟨add s.value (mul xy.1 xy.2),s.muls+4,s.adds+4⟩) ⟨(0,0),0,0⟩

/-- A row-matrix product whose arithmetic counters sum the counts from all component dot
products. -/
def rowCounted {D : ℕ} (v : Fin D→GI) (A : Matrix (Fin D) (Fin D) GI) : Counted (Fin D→GI) :=
  let ds := List.ofFn (fun j : Fin D=>dotCounted v A j)
  ⟨fun j=>(ds[j.val]?.getD ⟨(0,0),0,0⟩).value,(ds.map Counted.muls).sum,(ds.map Counted.adds).sum⟩

/-- Successive Gaussian integer row updates with cumulative multiplication and addition counts. -/
def runCounted {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : Counted (Fin D→GI) :=
  As.foldl (fun s A=>let t:=rowCounted s.value A;⟨t.value,s.muls+t.muls,s.adds+t.adds⟩) ⟨initial D,0,0⟩

end Qatlib.Concepts.DyadicProgram.DyadicContract
