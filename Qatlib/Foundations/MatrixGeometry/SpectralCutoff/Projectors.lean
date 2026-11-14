/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Hom.Esakia
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Finite-dimensional spectral cutoff projectors

Defines the eigenvalue mask `mask`, the spectral projector `low` for eigenvalues at most a real
threshold, and its complement `high`. Both projectors are Hermitian, idempotent, positive
semidefinite contractions; ordered thresholds give nesting and orthogonality of separated
spectral subspaces. See [HejaziZiniArrazola2024] for related background.

## Main statements

* `low_nested`: For `Δ ≤ Λ`, multiplying the low-energy projectors at `Δ` and `Λ` gives the
  projector at `Δ`.
* `separated_orthogonal`: For `Δ ≤ Λ`, the projector onto energies above `Λ` annihilates the
  projector onto energies at most `Δ`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix Unitary
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The diagonal indicator of eigenvalues of `H` that are at most `Δ`, in the eigenvector
coordinates supplied by `hH`. -/
def mask (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ :=
  diagonal (fun i=>if hH.eigenvalues i ≤ Δ then 1 else 0)

/-- The spectral projector of `H` onto eigenvalues at most `Δ`, obtained by conjugating `mask`
by the eigenvector unitary. -/
def low (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ :=
  conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary (mask H hH Δ)

/-- The complementary spectral projector `1 - low H hH Δ`. -/
def high (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) : Matrix I I ℂ := 1-low H hH Δ

/-- The diagonal eigenvalue mask is Hermitian. -/
theorem mask_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (mask H hH Δ)ᴴ=mask H hH Δ := by
  ext i j
  by_cases hij:i=j
  · subst j
    by_cases he:hH.eigenvalues i ≤ Δ <;> simp [mask,Matrix.conjTranspose_apply,he]
  · simp [mask,Matrix.conjTranspose_apply,hij,Ne.symm hij]

/-- The diagonal eigenvalue mask is idempotent. -/
theorem mask_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    mask H hH Δ*mask H hH Δ=mask H hH Δ := by
  rw [mask,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> norm_num

/-- The low-energy spectral projector is Hermitian. -/
theorem low_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (low H hH Δ)ᴴ=low H hH Δ := by
  change star (conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary (mask H hH Δ))=_
  rw [← map_star]
  exact congrArg _ (mask_hermitian H hH Δ)

/-- The low-energy spectral projector is idempotent. -/
theorem low_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    low H hH Δ*low H hH Δ=low H hH Δ := by
  exact (map_mul _ _ _).symm.trans (congrArg _ (mask_square H hH Δ))

/-- The low-energy spectral projector has operator norm at most one. -/
theorem low_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    ‖low H hH Δ‖ ≤ 1 := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self (low H hH Δ)
  rw [low_hermitian,low_square] at h
  nlinarith [norm_nonneg (low H hH Δ)]

/-- The complementary high-energy spectral projector is Hermitian. -/
theorem high_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (high H hH Δ)ᴴ=high H hH Δ := by simp only [high,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,low_hermitian]

/-- The complementary high-energy spectral projector is idempotent. -/
theorem high_square (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    high H hH Δ*high H hH Δ=high H hH Δ := by
  have h:=low_square H hH Δ
  unfold high
  noncomm_ring [h]

/-- The high-energy spectral projector has operator norm at most one. -/
theorem high_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    ‖high H hH Δ‖ ≤ 1 := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self (high H hH Δ)
  rw [high_hermitian,high_square] at h
  nlinarith [norm_nonneg (high H hH Δ)]

/-- The low-energy spectral projector is positive semidefinite. -/
theorem low_psd (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (low H hH Δ).PosSemidef := by
  have h:=Matrix.posSemidef_conjTranspose_mul_self (low H hH Δ)
  rwa [low_hermitian,low_square] at h

/-- The high-energy spectral projector is positive semidefinite. -/
theorem high_psd (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    (high H hH Δ).PosSemidef := by
  have h:=Matrix.posSemidef_conjTranspose_mul_self (high H hH Δ)
  rwa [high_hermitian,high_square] at h

/-- For `Δ ≤ Λ`, multiplying the low-energy projectors at `Δ` and `Λ` gives the projector at
`Δ`. -/
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

/-- For `Δ ≤ Λ`, the projector onto energies above `Λ` annihilates the projector onto energies
at most `Δ`. -/
theorem separated_orthogonal (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ Λ : ℝ) (h : Δ ≤ Λ) :
    high H hH Λ*low H hH Δ=0 := by
  have he:=low_nested H hH Δ Λ h
  have he':low H hH Λ*low H hH Δ=low H hH Δ := by
    have ht:=congrArg Matrix.conjTranspose he
    simpa only [Matrix.conjTranspose_mul,low_hermitian] using ht
  simp only [high,sub_mul,one_mul,he',sub_self]

end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
