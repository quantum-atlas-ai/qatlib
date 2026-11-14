/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Extending orthonormal columns to a unitary matrix

Proves `exists_unitary_extend_cols`, which completes a complex matrix with orthonormal columns
to a square unitary matrix. An injective map specifies the positions of the prescribed columns,
and the completion satisfies both unitary matrix identities. See [NielsenChuang2010] for related
background.

## Main statements

* `exists_unitary_extend_cols`: A complex matrix `W` with `W.conjTranspose * W = 1` extends to a
  square unitary matrix whose columns at the injectively specified positions `emb j` agree with
  the columns of `W`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.State

/-- A complex matrix `W` with `W.conjTranspose * W = 1` extends to a square unitary matrix whose
columns at the injectively specified positions `emb j` agree with the columns of `W`. -/
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
    rw [dite_eq_left (Set.mem_range_self j)]
    have h2 : (⟨emb j, _⟩ : Set.range emb) = equiv j := he.symm
    rw [h2]
    exact congrArg w (equiv.symm_apply_apply j)
  have hv : Orthonormal ℂ ((Set.range emb).domRestrict v) := by
    have hre : (Set.range emb).domRestrict v = w ∘ equiv.symm := by
      funext x
      show (if x.val ∈ Set.range emb then w (equiv.symm ⟨x.val, x.property⟩) else 0)
        = w (equiv.symm x)
      exact dite_eq_left x.property
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
