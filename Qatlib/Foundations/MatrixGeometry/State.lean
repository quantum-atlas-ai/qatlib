/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Set
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.State

theorem exists_unitary_extend_cols {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (W : Matrix ι (Fin d) ℂ) (emb : Fin d → ι) (hemb : Function.Injective emb)
    (hW : W.conjTranspose * W = 1) :
    ∃ U : Matrix ι ι ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      ∀ (x : ι) (j : Fin d), U x (emb j) = W x j := by
  classical
  let w : Fin d → EuclideanSpace ℂ ι := fun j => WithLp.toLp 2 (fun x => W x j)
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    show inner ℂ (WithLp.toLp 2 (fun x => W x i)) (WithLp.toLp 2 (fun x => W x j))
      = if i = j then (1 : ℂ) else 0
    rw [EuclideanSpace.inner_toLp_toLp]
    show (fun x => W x j) ⬝ᵥ star (fun x => W x i) = if i = j then (1 : ℂ) else 0
    rw [dotProduct_comm]
    have h1 : (star fun x => W x i) ⬝ᵥ (fun x => W x j) = (W.conjTranspose * W) i j := rfl
    rw [h1, hW, Matrix.one_apply]
  let equiv : Fin d ≃ Set.range emb := Equiv.ofInjective emb hemb
  let v : ι → EuclideanSpace ℂ ι := fun y =>
    if hy : y ∈ Set.range emb then w (equiv.symm ⟨y, hy⟩) else 0
  have hvapp (j : Fin d) : v (emb j) = w j := by
    have he : equiv j = (⟨emb j, Set.mem_range_self j⟩ : Set.range emb) :=
      Equiv.ofInjective_apply emb hemb j
    show (if h : emb j ∈ Set.range emb then w (equiv.symm ⟨emb j, h⟩) else 0) = w j
    rw [dif_pos (Set.mem_range_self j)]
    have h2 : (⟨emb j, _⟩ : Set.range emb) = equiv j := he.symm
    rw [h2]
    exact congrArg w (equiv.symm_apply_apply j)
  have hv : Orthonormal ℂ ((Set.range emb).restrict v) := by
    have hre : (Set.range emb).restrict v = w ∘ equiv.symm := by
      funext x
      show (if x.val ∈ Set.range emb then w (equiv.symm ⟨x.val, x.property⟩) else 0)
        = w (equiv.symm x)
      exact dif_pos x.property
    rw [hre]
    exact Orthonormal.comp hw equiv.symm (Equiv.injective equiv.symm)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := ι) (card_ι := finrank_euclideanSpace (𝕜 := ℂ) (ι := ι)) hv
  refine ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b, ?_, ?_, ?_⟩
  · exact OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
      (EuclideanSpace.basisFun ι ℂ) b
  · exact OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose
      (EuclideanSpace.basisFun ι ℂ) b
  · intro x j
    have hj : emb j ∈ Set.range emb := Set.mem_range_self j
    have hcol : ((EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b) x (emb j)
        = ⇑(b (emb j)) x := rfl
    rw [hcol, hb (emb j) hj, hvapp j]

end Qatlib.Foundations.MatrixGeometry.State
