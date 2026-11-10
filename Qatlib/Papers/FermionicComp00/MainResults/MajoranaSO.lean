/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.MajoranaSO

def sourceMajorana {m : ℕ} (j : Fin (2 * m)) : Matrix (Reg m) (Reg m) ℂ :=
  if j.val % 2 = 0 then
    creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ +
      annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩
  else
    (-Complex.I) •
      (annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ -
        creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩)

def sourceSO (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {β | βᵀ * β = 1 ∧ β * βᵀ = 1 ∧ Matrix.det β = 1}

theorem sourceSO_one_mem (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ sourceSO n := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · simp

def sourceQuadraticForm {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  ∑ j, ∑ k, A j k • (sourceMajorana j * sourceMajorana k)

def sourceQuadraticGate {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  NormedSpace.exp (Complex.I • sourceQuadraticForm A)

def sourceConj {m : ℕ} (U X : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  U * X * U.conjTranspose

inductive sourceQuadraticProduct {m : ℕ} : Matrix (Reg m) (Reg m) ℂ → Prop
  | one : sourceQuadraticProduct 1
  | gate {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ} (hA : Aᵀ = -A)
      {V : Matrix (Reg m) (Reg m) ℂ} (hV : sourceQuadraticProduct V) :
      sourceQuadraticProduct (sourceQuadraticGate A * V)

end Qatlib.Papers.FermionicComp00.MainResults.MajoranaSO
