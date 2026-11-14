/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Oriented selection and symmetric compression

`select` places the two ordered products `R * S` and `S * R` in opposite off-diagonal blocks.
For Hermitian involutions this matrix is itself a Hermitian unitary. The construction supplies
an explicit compression identity for the linear-combination framework of [GilyenSuLowWiebe2019].

`plusEmbedding` is the equal-superposition embedding into the two summands. Its compression of
`select R S` is the symmetrized product `(R * S + S * R) / 2`.

## Main statements

* `select_unitary`: oriented selection of Hermitian involutions is unitary.
* `plus_select_compression`: compute the equal-superposition compression.
* `plus_select_one`: recover `R` when the second input is the identity.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The off-diagonal block matrix with ordered products `R * S` and `S * R`. -/
def select (R S : Matrix I I ℂ) : Matrix (Sum I I) (Sum I I) ℂ :=
  Matrix.fromBlocks 0 (R*S) (S*R) 0

/-- The real amplitude `1 / √2`, regarded as a complex number. -/
def plusAmplitude : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The embedding with equal amplitude `1 / √2` in each of the two summands. -/
def plusEmbedding : Matrix (Sum I I) I ℂ :=
  Matrix.fromRows (plusAmplitude • (1 : Matrix I I ℂ)) (plusAmplitude • 1)

/-- The equal-superposition amplitude is fixed by complex conjugation. -/
theorem plusAmplitude_star : star plusAmplitude=plusAmplitude := by
  simp [plusAmplitude]

/-- The square of the equal-superposition amplitude is `1 / 2`. -/
theorem plusAmplitude_square : plusAmplitude*plusAmplitude=(1/2:ℂ) := by
  have hr : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹=(1/2:ℝ) := by
    rw [← pow_two,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  unfold plusAmplitude
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

/-- Oriented selection is an involution when both input matrices are involutions. -/
theorem select_square (R S : Matrix I I ℂ) (hR : R*R=1) (hS : S*S=1) :
    select R S*select R S=1 := by
  have hrs : R*S*(S*R)=1 := by
    calc
      _ = R*(S*S)*R := by noncomm_ring
      _ = 1 := by rw [hS]; simp [hR]
  have hsr : S*R*(R*S)=1 := by
    calc
      _ = S*(R*R)*S := by noncomm_ring
      _ = 1 := by rw [hR]; simp [hS]
  simp [select,Matrix.fromBlocks_multiply,hrs,hsr,Matrix.fromBlocks_one]

omit [DecidableEq I] in

/-- Oriented selection is Hermitian when both input matrices are Hermitian. -/
theorem select_hermitian (R S : Matrix I I ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian) :
    (select R S).IsHermitian := by
  change (select R S)ᴴ=select R S
  simp [select,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_mul,hR.eq,hS.eq]

/-- Oriented selection of two Hermitian involutions is unitary. -/
theorem select_unitary (R S : Matrix I I ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hRR : R*R=1) (hSS : S*S=1) :
    select R S∈Matrix.unitaryGroup (Sum I I) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change select R S*(select R S)ᴴ=1
  rw [(select_hermitian R S hR hS).eq]
  exact select_square R S hRR hSS

/-- The equal-superposition embedding has conjugate-transpose product equal to the identity. -/
theorem plusEmbedding_isometry :
    (plusEmbedding (I:=I))ᴴ*plusEmbedding (I:=I)=1 := by
  simp only [plusEmbedding,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,plusAmplitude_star,
    Matrix.fromCols_mul_fromRows,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    smul_smul,plusAmplitude_square]
  rw [← add_smul]
  norm_num

/-- Compression of oriented selection through `plusEmbedding` gives `(1 / 2) • (R * S + S * R)`. -/
theorem plus_select_compression (R S : Matrix I I ℂ) :
    (plusEmbedding (I:=I))ᴴ*select R S*plusEmbedding (I:=I)=(1/2:ℂ) • (R*S+S*R) := by
  simp only [plusEmbedding,select,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,plusAmplitude_star,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,Matrix.mul_zero,
    zero_add,add_zero,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    Matrix.mul_one,smul_smul,plusAmplitude_square]
  module

/-- Compression of `select R 1` through `plusEmbedding` recovers `R`. -/
theorem plus_select_one (R : Matrix I I ℂ) :
    (plusEmbedding (I:=I))ᴴ*select R 1*plusEmbedding (I:=I)=R := by
  rw [plus_select_compression]
  simp only [Matrix.mul_one,Matrix.one_mul,← two_smul ℂ R,smul_smul]
  norm_num

end Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
