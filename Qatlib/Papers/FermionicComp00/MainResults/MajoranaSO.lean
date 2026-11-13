/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Quadratic Majorana operators and special orthogonal matrices

The module defines real special orthogonal matrices as `sourceSO` and builds quadratic
expressions in `sourceMajorana`. It introduces their matrix exponentials, conjugation, and the
finite-product predicate `sourceQuadraticProduct` with skew-symmetric coefficient matrices.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `sourceSO_one_mem`: the identity is special orthogonal.
* `sourceQuadraticProduct`: products of quadratic Majorana exponentials.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.MajoranaSO

/-- The Majorana matrix at index `j`, given by creation plus annihilation at even indices and by
negative imaginary times annihilation minus creation at odd indices. -/
def sourceMajorana {m : ℕ} (j : Fin (2 * m)) : Matrix (Reg m) (Reg m) ℂ :=
  if j.val % 2 = 0 then
    creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ +
      annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩
  else
    (-Complex.I) •
      (annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ -
        creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩)

/-- The set of real matrices whose transpose is a two-sided inverse and whose determinant is
one. -/
def sourceSO (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {β | βᵀ * β = 1 ∧ β * βᵀ = 1 ∧ Matrix.det β = 1}

/-- The identity matrix belongs to `sourceSO n`. -/
theorem sourceSO_one_mem (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ sourceSO n := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · simp

/-- The double sum of ordered Majorana products weighted by the entries of `A`. -/
def sourceQuadraticForm {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  ∑ j, ∑ k, A j k • (sourceMajorana j * sourceMajorana k)

/-- The matrix exponential of `Complex.I` times the quadratic Majorana expression associated
with `A`. -/
def sourceQuadraticGate {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  NormedSpace.exp (Complex.I • sourceQuadraticForm A)

/-- Conjugation of `X` by `U`, defined as `U * X * U.conjTranspose`. -/
def sourceConj {m : ℕ} (U X : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  U * X * U.conjTranspose

/-- Matrices generated from the identity by left multiplication with quadratic Majorana
exponentials having skew-symmetric complex coefficient matrices. -/
inductive sourceQuadraticProduct {m : ℕ} : Matrix (Reg m) (Reg m) ℂ → Prop
  | one : sourceQuadraticProduct 1
  | gate {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ} (hA : Aᵀ = -A)
      {V : Matrix (Reg m) (Reg m) ℂ} (hV : sourceQuadraticProduct V) :
      sourceQuadraticProduct (sourceQuadraticGate A * V)

end Qatlib.Papers.FermionicComp00.MainResults.MajoranaSO
