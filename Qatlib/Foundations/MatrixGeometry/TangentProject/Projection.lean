/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Orthogonal projection onto unitary tangent spaces

Defines the real Frobenius pairing `realFrob`, the Hermitian and skew-Hermitian parts of a
matrix, and tangent vectors of the form `Ω * U` with skew-Hermitian `Ω`. For unitary `U`,
`project U Z` is tangent, its residual is orthogonal to every tangent vector, and it fixes
tangent vectors. See [LaiEtAl2026] for related background.

## Main statements

* `project_orthogonal`: For unitary `U`, the residual `Z - project U Z` is orthogonal to every
  tangent vector at `U` under the real Frobenius pairing.
* `project_eq_self`: For unitary `U`, tangent projection fixes every tangent vector at `U`.

## References

* [Lai et al., 2026][LaiEtAl2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixGeometry.TangentProject
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Frobenius pairing `Re Tr(Aᴴ * B)` on complex matrices. -/
def realFrob (A B : Matrix n n ℂ) : ℝ := (Aᴴ * B).trace.re

/-- The skew-Hermitian part `½ • (A - Aᴴ)` of a complex matrix. -/
def skew (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • (A - Aᴴ)

/-- The Hermitian part `½ • (A + Aᴴ)` of a complex matrix. -/
def herm (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • (A + Aᴴ)

/-- The condition that `V = Ω * U` for some skew-Hermitian matrix `Ω`. -/
def IsTangent (U V : Matrix n n ℂ) : Prop :=
  ∃ Ω : Matrix n n ℂ, Ωᴴ = -Ω ∧ V = Ω * U

/-- The matrix expression `skew (Z * Uᴴ) * U`, giving tangent projection when `U` is unitary. -/
def project (U Z : Matrix n n ℂ) : Matrix n n ℂ := skew (Z * Uᴴ) * U

omit [Fintype n] [DecidableEq n] in

/-- The conjugate transpose of the skew-Hermitian part is its negative. -/
theorem skew_adjoint (A : Matrix n n ℂ) : (skew A)ᴴ = -skew A := by
  simp only [skew, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]

omit [Fintype n] [DecidableEq n] in

/-- The Hermitian part is fixed by conjugate transpose. -/
theorem herm_adjoint (A : Matrix n n ℂ) : (herm A)ᴴ = herm A := by
  simp only [herm, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

omit [DecidableEq n] in

/-- The expression `project U Z` is tangent at `U` in the sense of `IsTangent`. -/
theorem project_tangent (U Z : Matrix n n ℂ) : IsTangent U (project U Z) :=
  ⟨skew (Z * Uᴴ), skew_adjoint _, rfl⟩

omit [DecidableEq n] in

/-- A Hermitian matrix and a skew-Hermitian matrix have zero real Frobenius pairing. -/
theorem realFrob_herm_skew (H K : Matrix n n ℂ) (hH : Hᴴ = H) (hK : Kᴴ = -K) :
    realFrob H K = 0 := by
  have hc : star (H * K).trace = -(H * K).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH, hK,
      neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hr := congrArg Complex.re hc
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  simp only [realFrob, hH]
  linarith

/-- Right multiplication of both arguments by a unitary matrix preserves their real Frobenius
pairing. -/
theorem realFrob_mul_unitary (U A B : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    realFrob (A * U) (B * U) = realFrob A B := by
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  simp only [realFrob, Matrix.conjTranspose_mul]
  rw [show Uᴴ * Aᴴ * (B * U) = Uᴴ * (Aᴴ * B * U) by noncomm_ring,
    Matrix.trace_mul_comm Uᴴ, Matrix.mul_assoc (Aᴴ * B) U Uᴴ, hu, Matrix.mul_one]

/-- For unitary `U`, the residual `Z - project U Z` is `herm (Z * Uᴴ) * U`. -/
theorem project_residual (U Z : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Z - project U Z = herm (Z * Uᴴ) * U := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hz : Z * Uᴴ * U = Z := by rw [Matrix.mul_assoc, hu, Matrix.mul_one]
  simp only [project, skew, herm, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul]
  rw [hz]
  module

/-- For unitary `U`, the residual `Z - project U Z` is orthogonal to every tangent vector at `U`
under the real Frobenius pairing. -/
theorem project_orthogonal (U Z V : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hV : IsTangent U V) : realFrob (Z - project U Z) V = 0 := by
  obtain ⟨Ω, hΩ, rfl⟩ := hV
  rw [project_residual U Z hU, realFrob_mul_unitary U _ _ hU]
  exact realFrob_herm_skew _ _ (herm_adjoint _) hΩ

/-- For unitary `U`, tangent projection fixes every tangent vector at `U`. -/
theorem project_eq_self (U V : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hV : IsTangent U V) : project U V = V := by
  obtain ⟨Ω, hΩ, rfl⟩ := hV
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  simp only [project, Matrix.mul_assoc, hu, Matrix.mul_one, skew, hΩ, sub_neg_eq_add]
  congr 1
  module

omit [DecidableEq n] in

/-- The real Frobenius pairing distributes over subtraction in its first argument. -/
theorem realFrob_sub_left (A B C : Matrix n n ℂ) :
    realFrob (A - B) C = realFrob A C - realFrob B C := by
  simp only [realFrob, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
