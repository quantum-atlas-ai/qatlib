/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix

abbrev State (I : Type*) := I → ℂ

def Inner {I : Type*} [Fintype I] (u v : State I) : ℂ := star u ⬝ᵥ v

def Normalized {I : Type*} [Fintype I] (u : State I) : Prop := ∑ i, ‖u i‖^2=1

def toHilbert {I : Type*} (u : State I) : EuclideanSpace ℂ I := WithLp.toLp 2 u

theorem inner_apply {I : Type*} [Fintype I] (u v : State I) :
    Inner u v = ∑ i, (starRingEnd ℂ) (u i) * v i := by
  simp only [Inner, dotProduct, Pi.star_apply, RCLike.star_def]

theorem inner_toHilbert {I : Type*} [Fintype I] (u v : State I) :
    inner ℂ (toHilbert u) (toHilbert v) = Inner u v := by
  simp [toHilbert, EuclideanSpace.inner_toLp_toLp, Inner, dotProduct_comm]

theorem normalized_iff_hilbert {I : Type*} [Fintype I] (u : State I) :
    Normalized u ↔ ‖toHilbert u‖=1 := by
  have h := EuclideanSpace.norm_sq_eq (toHilbert u)
  change ‖toHilbert u‖^2 = ∑ i, ‖u i‖^2 at h
  unfold Normalized
  constructor <;> intro hh
  · nlinarith [norm_nonneg (toHilbert u)]
  · nlinarith

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
