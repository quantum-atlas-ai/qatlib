/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Basic
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Gaussian-map parameters and correlation updates

`GaussianMap` packages a Fock-space linear map, a scalar, three matrix parameters, and a
representation proposition. This module defines the associated block matrix, positivity
predicates, finite Kraus representations, and two rational correlation-update formulas.

`TensorProductMaps` records ordinary and fermionic extension maps on the doubled-mode space.
These results formalize the indicated identities from [Bravyi2005Fermionic].

## Main statements

* `lambdaCommute`: expresses commutation of a tensor square with `Lambda`.
* `IsCP`: expresses existence of a finite Kraus representation.
* `corrUpdate` and `corrUpdate'`: define the two matrix-inverse update expressions.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

/-- The condition that the tensor square of `X` commutes with `Lambda n`. -/
noncomputable def lambdaCommute {n : ℕ} (X : Fock n) : Prop :=
  Lambda n * tensorSquare X = tensorSquare X * Lambda n

/-- A Fock-space linear map together with scalar and matrix parameters `C`, `A`, `B`, `D`, and a
proposition `hasRep` for representation data. -/
structure GaussianMap (n : ℕ) where

  toFun : Fock n →ₗ[ℂ] Fock n

  C : ℂ

  A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  hasRep : Prop

/-- The block matrix with blocks `A`, `B`, `-Bᵀ`, and `D`. -/
noncomputable def blockM {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix (Fin (2 * (2 * n))) (Fin (2 * (2 * n))) ℂ :=
  fun i j =>
    if hi : (i : ℕ) < 2 * n then
      if hj : (j : ℕ) < 2 * n then A ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
      else B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ) - 2 * n, by
        have hj' : (j : ℕ) < 2 * (2 * n) := j.isLt
        omega⟩
    else
      if hj : (j : ℕ) < 2 * n then
        -(B ⟨(j : ℕ), hj⟩ ⟨(i : ℕ) - 2 * n, by
          have hi' : (i : ℕ) < 2 * (2 * n) := i.isLt
          omega⟩)
      else D ⟨(i : ℕ) - 2 * n, by
                have hi' : (i : ℕ) < 2 * (2 * n) := i.isLt
                omega⟩
               ⟨(j : ℕ) - 2 * n, by
                have hj' : (j : ℕ) < 2 * (2 * n) := j.isLt
                omega⟩

/-- The condition that every entry of the block matrix with blocks `A`, `B`, `-Bᵀ`, and `D` has
zero imaginary part. -/
noncomputable def blockMReal {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop :=
  ∀ i j, ((blockM A B D) i j).im = 0

/-- The condition that a linear map preserves positive semidefinite operators. -/
noncomputable def IsPositiveMap {n : ℕ} (F : Fock n →ₗ[ℂ] Fock n) : Prop :=
  ∀ X : Fock n, IsPositiveOperator X → IsPositiveOperator (F X)

/-- The existence of a finite Kraus representation `F X = ∑ a, A a * X * (A a)ᴴ`. -/
noncomputable def IsCP {n : ℕ} (F : Fock n →ₗ[ℂ] Fock n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → Fock n), ∀ X : Fock n, F X = ∑ a, A a * X * (A a)ᴴ

/-- The correlation-update expression `B * (M⁻¹ + D)⁻¹ * Bᵀ + A`. -/
noncomputable def corrUpdate {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  B * (M⁻¹ + D)⁻¹ * Bᵀ + A

/-- The alternative correlation-update expression `B * (1 + M * D)⁻¹ * M * Bᵀ + A`. -/
noncomputable def corrUpdate' {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  B * (1 + M * D)⁻¹ * M * Bᵀ + A

/-- A pair of linear maps on the doubled-mode Fock space, designated as the ordinary and
fermionic extensions for `E`. -/
structure TensorProductMaps {n : ℕ} (E : GaussianMap n) where

  ordinary : Fock (2 * n) →ₗ[ℂ] Fock (2 * n)

  fermionic : Fock (2 * n) →ₗ[ℂ] Fock (2 * n)

end Qatlib.Papers.FermLinOpt04.MainResults.Model
