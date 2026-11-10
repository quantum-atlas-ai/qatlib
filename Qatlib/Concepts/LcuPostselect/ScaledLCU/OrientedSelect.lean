/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def select (R S : Matrix I I ℂ) : Matrix (Sum I I) (Sum I I) ℂ :=
  Matrix.fromBlocks 0 (R*S) (S*R) 0

def plusAmplitude : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

def plusEmbedding : Matrix (Sum I I) I ℂ :=
  Matrix.fromRows (plusAmplitude • (1 : Matrix I I ℂ)) (plusAmplitude • 1)

theorem plusAmplitude_star : star plusAmplitude=plusAmplitude := by
  simp [plusAmplitude]

theorem plusAmplitude_square : plusAmplitude*plusAmplitude=(1/2:ℂ) := by
  have hr : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹=(1/2:ℝ) := by
    rw [← pow_two,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  unfold plusAmplitude
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

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

theorem select_hermitian (R S : Matrix I I ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian) :
    (select R S).IsHermitian := by
  change (select R S)ᴴ=select R S
  simp [select,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_mul,hR.eq,hS.eq]

theorem select_unitary (R S : Matrix I I ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hRR : R*R=1) (hSS : S*S=1) :
    select R S∈Matrix.unitaryGroup (Sum I I) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change select R S*(select R S)ᴴ=1
  rw [(select_hermitian R S hR hS).eq]
  exact select_square R S hRR hSS

theorem plusEmbedding_isometry :
    (plusEmbedding (I:=I))ᴴ*plusEmbedding (I:=I)=1 := by
  simp only [plusEmbedding,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,plusAmplitude_star,
    Matrix.fromCols_mul_fromRows,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    smul_smul,plusAmplitude_square]
  rw [← add_smul]
  norm_num

theorem plus_select_compression (R S : Matrix I I ℂ) :
    (plusEmbedding (I:=I))ᴴ*select R S*plusEmbedding (I:=I)=(1/2:ℂ) • (R*S+S*R) := by
  simp only [plusEmbedding,select,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,plusAmplitude_star,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,Matrix.mul_zero,
    zero_add,add_zero,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    Matrix.mul_one,smul_smul,plusAmplitude_square]
  module

theorem plus_select_one (R : Matrix I I ℂ) :
    (plusEmbedding (I:=I))ᴴ*select R 1*plusEmbedding (I:=I)=R := by
  rw [plus_select_compression]
  simp only [Matrix.mul_one,Matrix.one_mul,← two_smul ℂ R,smul_smul]
  norm_num

end Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
