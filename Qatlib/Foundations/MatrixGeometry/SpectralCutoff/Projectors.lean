/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix Unitary
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]

def mask (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ :=
  diagonal (fun i=>if hH.eigenvalues i ≤ Δ then 1 else 0)

def low (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ :=
  conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary (mask H hH Δ)

def high (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ := 1-low H hH Δ

theorem mask_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (mask H hH Δ)ᴴ=mask H hH Δ := by
  ext i j
  by_cases hij:i=j
  · subst j
    by_cases he:hH.eigenvalues i ≤ Δ <;> simp [mask,Matrix.conjTranspose_apply,he]
  · simp [mask,Matrix.conjTranspose_apply,hij,Ne.symm hij]

theorem mask_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    mask H hH Δ*mask H hH Δ=mask H hH Δ := by
  rw [mask,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> norm_num

theorem low_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (low H hH Δ)ᴴ=low H hH Δ := by
  change star (conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary (mask H hH Δ))=_
  rw [← map_star]
  exact congrArg _ (mask_hermitian H hH Δ)

theorem low_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    low H hH Δ*low H hH Δ=low H hH Δ := by
  exact (map_mul _ _ _).symm.trans (congrArg _ (mask_square H hH Δ))

theorem low_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    ‖low H hH Δ‖ ≤ 1 := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self (low H hH Δ)
  rw [low_hermitian,low_square] at h
  nlinarith [norm_nonneg (low H hH Δ)]

theorem high_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (high H hH Δ)ᴴ=high H hH Δ := by simp only [high,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,low_hermitian]

theorem high_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    high H hH Δ*high H hH Δ=high H hH Δ := by
  have h:=low_square H hH Δ
  unfold high
  noncomm_ring [h]

theorem high_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    ‖high H hH Δ‖ ≤ 1 := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self (high H hH Δ)
  rw [high_hermitian,high_square] at h
  nlinarith [norm_nonneg (high H hH Δ)]

theorem low_psd (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (low H hH Δ).PosSemidef := by
  have h:=Matrix.posSemidef_conjTranspose_mul_self (low H hH Δ)
  rwa [low_hermitian,low_square] at h

theorem high_psd (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (high H hH Δ).PosSemidef := by
  have h:=Matrix.posSemidef_conjTranspose_mul_self (high H hH Δ)
  rwa [high_hermitian,high_square] at h

theorem low_nested (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ Λ : ℝ) (h : Δ ≤ Λ) :
    low H hH Δ*low H hH Λ=low H hH Δ := by
  unfold low
  rw [← map_mul]
  apply congrArg
  rw [mask,mask,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi:hH.eigenvalues i ≤ Δ
  · simp [hi,hi.trans h]
  · simp [hi]

theorem separated_orthogonal (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ Λ : ℝ) (h : Δ ≤ Λ) :
    high H hH Λ*low H hH Δ=0 := by
  have he:=low_nested H hH Δ Λ h
  have he':low H hH Λ*low H hH Δ=low H hH Δ := by
    have ht:=congrArg Matrix.conjTranspose he
    simpa only [Matrix.conjTranspose_mul,low_hermitian] using ht
  simp only [high,sub_mul,one_mul,he',sub_self]

end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
