/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators
open Finset

def tuttePoly {E : Type*} [Fintype E] (k : Finset E → ℕ) (q : ℂ) (v : E → ℂ) : ℂ :=
  ∑ A : Finset E, q ^ (k A) * A.prod (fun e => v e)

def pottsPartition {E : Type*} [Fintype E] (k : Finset E → ℕ) (q : ℂ) (v : E → ℂ) : ℂ :=
  tuttePoly k q v

def kauffmanTerm {E : Type*} [Fintype E] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ)
    (A : Finset E) : ℂ :=
  d ^ (loops A) * A.prod (fun e => u e)

def kauffmanBracket {E : Type*} [Fintype E] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) : ℂ :=
  ∑ A : Finset E, kauffmanTerm loops d u A

variable {E : Type*} [Fintype E]

def psiOp {A : Type*} [CommRing A] [Algebra ℂ A] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) : A :=
  ∑ A' : Finset E, algebraMap ℂ A (kauffmanTerm loops d u A')

theorem psiOp_eq_scalar_mul_one {A : Type*} [CommRing A] [Algebra ℂ A]
    (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    psiOp (A := A) loops d u = kauffmanBracket loops d u • (1 : A) := by
  rw [psiOp, kauffmanBracket, Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro A' _
  rw [Algebra.algebraMap_eq_smul_one]

structure PathCoeffs (ι : Type*) where

  a : ι → ι → ℂ

  b : ι → ι → ℂ

  d : ℂ

def sigmaOdd {A : Type*} [CommRing A] [Algebra ℂ A] (u : ℂ) (Φ : A) : A :=
  algebraMap ℂ A u * (1 : A) + Φ

def sigmaEven {A : Type*} [CommRing A] [Algebra ℂ A] (u : ℂ) (Φ : A) : A :=
  (1 : A) + algebraMap ℂ A u * Φ

def expectationOne (Q : Matrix (Fin 1) (Fin 1) ℂ) : ℂ := Q 0 0

def IsUnitary {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) : Prop :=
  U * Matrix.conjTranspose U = 1 ∧ Matrix.conjTranspose U * U = 1

end Qatlib.Papers.PottsTutte07.MainResults
