/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.TableAccess.ReversibleTable
variable {I : Type*} [Fintype I] [DecidableEq I]

def Ket (j : I) : I→ℂ := fun i=>if i=j then 1 else 0

def permMatrix (σ : I → I) : Matrix I I ℂ := Matrix.of fun i j => if i = σ j then (1 : ℂ) else 0

theorem permMatrix_mul_self {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ * permMatrix σ = 1 := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ j) (fun k _ hk => by rw [if_neg hk, mul_zero])
    (fun h => absurd (Finset.mem_univ (σ j)) h)]
  simp [hσ j]

omit [Fintype I] in

theorem permMatrix_conjTranspose {σ : I → I} (hσ : Function.Involutive σ) :
    (permMatrix σ)ᴴ = permMatrix σ := by
  ext i j
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  by_cases hji : j = σ i
  · have hij : i = σ j := by rw [← hσ i, ← hji]
    rw [if_pos hji, if_pos hij, map_one]
  · have hij : i ≠ σ j := fun e => hji (by rw [← hσ j, ← e])
    rw [if_neg hji, if_neg hij, map_zero]

theorem permMatrix_unitary {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, permMatrix_conjTranspose hσ]
  exact permMatrix_mul_self hσ

theorem applyGate_permMatrix {σ : I → I} (hσ : Function.Involutive σ) (ψ : I→ℂ) (i : I) :
    (permMatrix σ *ᵥ ψ) i = ψ (σ i) := by
  simp only [permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · rw [hσ i]
    simp
  · intro j _ hj
    have hne : i ≠ σ j := fun h => hj (by rw [← hσ j, ← h])
    simp [hne]
  · simp

theorem applyGate_permMatrix_ket {σ : I → I} (hσ : Function.Involutive σ) (j : I) :
    (permMatrix σ) *ᵥ (Ket j) = Ket (σ j) := by
  funext i
  rw [applyGate_permMatrix hσ]
  by_cases h : i = σ j
  · subst h
    simp [Ket, hσ j]
  · have h' : σ i ≠ j := fun e => h (by rw [← e, hσ i])
    simp [Ket, h, h']

end Qatlib.Foundations.TableAccess.ReversibleTable
