/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Finite complex states for LCU frames

`State` represents finite complex coordinate vectors, with `Inner` and `Normalized` expressing
the complex inner product and squared-amplitude normalization. `toHilbert` converts these
coordinates to complex Euclidean space, and the module proves that inner products and unit norms
agree under this conversion.

`inner_mulVec_left_rect` gives the adjoint identity for rectangular matrix actions. These
coordinate identities provide the Hilbert-space foundations for the LCU frame calculations
associated with [PoulinEtAl2018].

## Main statements

* `inner_toHilbert`: coordinate and Euclidean inner products agree.
* `normalized_iff_hilbert`: squared-amplitude normalization is equivalent to Hilbert norm one.
* `inner_mulVec_left_rect`: rectangular matrix action transfers across the inner product by
  conjugate transpose.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix

/-- Complex coordinate vectors indexed by `I`. -/
abbrev State (I : Type*) := I → ℂ

/-- The finite complex inner product, conjugate-linear in its first coordinate vector. -/
def Inner {I : Type*} [Fintype I] (u v : State I) : ℂ := star u ⬝ᵥ v

/-- The condition that the sum of squared coordinate norms is one. -/
def Normalized {I : Type*} [Fintype I] (u : State I) : Prop := ∑ i, ‖u i‖^2=1

/-- The coordinate vector regarded as an element of complex Euclidean space. -/
def toHilbert {I : Type*} (u : State I) : EuclideanSpace ℂ I := WithLp.toLp 2 u

/-- The coordinate inner product is the sum of conjugated first coordinates times second
coordinates. -/
theorem inner_apply {I : Type*} [Fintype I] (u v : State I) :
    Inner u v = ∑ i, (starRingEnd ℂ) (u i) * v i := by
  simp only [Inner, dotProduct, Pi.star_apply, RCLike.star_def]

/-- Converting coordinate vectors to Euclidean space preserves their complex inner product. -/
theorem inner_toHilbert {I : Type*} [Fintype I] (u v : State I) :
    inner ℂ (toHilbert u) (toHilbert v) = Inner u v := by
  simp [toHilbert, EuclideanSpace.inner_toLp_toLp, Inner, dotProduct_comm]

/-- A finite coordinate vector is normalized exactly when its Euclidean realization has norm
one. -/
theorem normalized_iff_hilbert {I : Type*} [Fintype I] (u : State I) :
    Normalized u ↔ ‖toHilbert u‖=1 := by
  have h := EuclideanSpace.norm_sq_eq (toHilbert u)
  change ‖toHilbert u‖^2 = ∑ i, ‖u i‖^2 at h
  unfold Normalized
  constructor <;> intro hh
  · nlinarith [norm_nonneg (toHilbert u)]
  · nlinarith

/-- The inner product of `M *ᵥ ψ` with `φ` equals the inner product of `ψ` with `Mᴴ *ᵥ φ` for
any finite rectangular complex matrix. -/
theorem inner_mulVec_left_rect {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] (M : Matrix K I ℂ) (ψ : State I) (φ : State K) :
    Inner (M *ᵥ ψ) φ = Inner ψ (Mᴴ *ᵥ φ) := by
  have hL : ∀ k, (starRingEnd ℂ) ((M *ᵥ ψ) k) * φ k
      = ∑ i, (starRingEnd ℂ) (M k i) * ((starRingEnd ℂ) (ψ i)) * φ k := by
    intro k
    rw [show (M *ᵥ ψ) k = ∑ i, M k i * ψ i from by simp [Matrix.mulVec, dotProduct]]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by rw [map_mul]
  have hR : ∀ i, (starRingEnd ℂ) (ψ i) * ((Mᴴ *ᵥ φ) i)
      = ∑ k, (starRingEnd ℂ) (ψ i) * ((starRingEnd ℂ) (M k i) * φ k) := by
    intro i
    rw [show (Mᴴ *ᵥ φ) i = ∑ k, (starRingEnd ℂ) (M k i) * φ k from by
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def]]
    rw [Finset.mul_sum]
  rw [inner_apply, inner_apply]
  refine (Finset.sum_congr rfl fun k _ => hL k).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Finset.sum_congr rfl fun k _ => by ring).trans (hR i).symm
end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
