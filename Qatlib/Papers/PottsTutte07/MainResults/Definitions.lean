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

/-!
# Tutte subset sums and scalar operators

The multivariate subset sum `tuttePoly` and the loop-weighted sum `kauffmanBracket` provide the
scalar partition expressions used here. The algebra-valued sum `psiOp` is shown to be the
bracket times the identity, and the module defines odd and even local operators together with
matrix unitarity [AharonovEtAl2007].

## Main statements

* `psiOp_eq_scalar_mul_one`: The algebra-valued subset sum is a scalar multiple of the identity.
* `sigmaOdd`: The odd local operator adds its algebra element to the scalar identity.
* `IsUnitary`: Both products with the conjugate transpose equal the identity.

## References

* [Aharonov et al., 2007][AharonovEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators
open Finset

/-- The multivariate subset sum of `q ^ k A` times the product of the edge weights in `A`. -/
def tuttePoly {E : Type*} [Fintype E] (k : Finset E → ℕ) (q : ℂ) (v : E → ℂ) : ℂ :=
  ∑ A : Finset E, q ^ (k A) * A.prod (fun e => v e)

/-- The Potts partition expression defined by the multivariate Tutte subset sum. -/
def pottsPartition {E : Type*} [Fintype E] (k : Finset E → ℕ) (q : ℂ) (v : E → ℂ) : ℂ :=
  tuttePoly k q v

/-- The Kauffman state contribution `d ^ loops A` times the product of selected weights. -/
def kauffmanTerm {E : Type*} [Fintype E] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ)
    (A : Finset E) : ℂ :=
  d ^ (loops A) * A.prod (fun e => u e)

/-- The sum of the Kauffman state contributions over all edge subsets. -/
def kauffmanBracket {E : Type*} [Fintype E] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) : ℂ :=
  ∑ A : Finset E, kauffmanTerm loops d u A

variable {E : Type*} [Fintype E]

/-- The algebra-valued sum obtained by embedding each Kauffman state contribution into the
algebra. -/
def psiOp {A : Type*} [CommRing A] [Algebra ℂ A] (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) : A :=
  ∑ A' : Finset E, algebraMap ℂ A (kauffmanTerm loops d u A')

/-- The operator sum `psiOp` is the Kauffman bracket times the algebra identity. -/
theorem psiOp_eq_scalar_mul_one {A : Type*} [CommRing A] [Algebra ℂ A]
    (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    psiOp (A := A) loops d u = kauffmanBracket loops d u • (1 : A) := by
  rw [psiOp, kauffmanBracket, Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro A' _
  rw [Algebra.algebraMap_eq_smul_one]

/-- A record of two families of complex path coefficients and a complex loop parameter. -/
structure PathCoeffs (ι : Type*) where

  a : ι → ι → ℂ

  b : ι → ι → ℂ

  d : ℂ

/-- The odd local operator `u * 1 + Φ`, with the scalar embedded into the algebra. -/
def sigmaOdd {A : Type*} [CommRing A] [Algebra ℂ A] (u : ℂ) (Φ : A) : A :=
  algebraMap ℂ A u * (1 : A) + Φ

/-- The even local operator `1 + u * Φ`, with the scalar embedded into the algebra. -/
def sigmaEven {A : Type*} [CommRing A] [Algebra ℂ A] (u : ℂ) (Φ : A) : A :=
  (1 : A) + algebraMap ℂ A u * Φ

/-- The sole matrix entry of a complex matrix indexed by `Fin 1`. -/
def expectationOne (Q : Matrix (Fin 1) (Fin 1) ℂ) : ℂ := Q 0 0

/-- The condition that multiplication by the conjugate transpose on either side gives the
identity. -/
def IsUnitary {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) : Prop :=
  U * Matrix.conjTranspose U = 1 ∧ Matrix.conjTranspose U * U = 1

end Qatlib.Papers.PottsTutte07.MainResults
