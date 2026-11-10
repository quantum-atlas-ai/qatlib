/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Basic
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

noncomputable def lambdaCommute {n : ℕ} (X : Fock n) : Prop :=
  Lambda n * tensorSquare X = tensorSquare X * Lambda n

structure GaussianMap (n : ℕ) where

  toFun : Fock n →ₗ[ℂ] Fock n

  C : ℂ

  A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ

  hasRep : Prop

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

noncomputable def blockMReal {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop :=
  ∀ i j, ((blockM A B D) i j).im = 0

noncomputable def IsPositiveMap {n : ℕ} (F : Fock n →ₗ[ℂ] Fock n) : Prop :=
  ∀ X : Fock n, IsPositiveOperator X → IsPositiveOperator (F X)

noncomputable def IsCP {n : ℕ} (F : Fock n →ₗ[ℂ] Fock n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → Fock n), ∀ X : Fock n, F X = ∑ a, A a * X * (A a)ᴴ

noncomputable def corrUpdate {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  B * (M⁻¹ + D)⁻¹ * Bᵀ + A

noncomputable def corrUpdate' {n : ℕ} (A B D : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  B * (1 + M * D)⁻¹ * M * Bᵀ + A

structure TensorProductMaps {n : ℕ} (E : GaussianMap n) where

  ordinary : Fock (2 * n) →ₗ[ℂ] Fock (2 * n)

  fermionic : Fock (2 * n) →ₗ[ℂ] Fock (2 * n)

end Qatlib.Papers.FermLinOpt04.MainResults.Model
