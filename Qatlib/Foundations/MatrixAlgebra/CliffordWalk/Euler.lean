/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixAlgebra.CliffordWalk

noncomputable def pauliHom {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (hP : P * P = 1) : ℂ →ₐ[ℝ] Matrix I I ℂ :=
  Complex.liftAux (Complex.I • P) (by
    rw [smul_mul_smul, hP, Complex.I_mul_I]
    simp)

@[simp]
theorem pauliHom_apply {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (hP : P * P = 1) (z : ℂ) :
    pauliHom P hP z = algebraMap ℝ (Matrix I I ℂ) z.re + z.im • (Complex.I • P) :=
  Complex.liftAux_apply _ _ z

theorem exp_euler {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (hP : P * P = 1) (θ : ℝ) :
    NormedSpace.exp (θ • (Complex.I • P)) =
      (Real.cos θ) • (1 : Matrix I I ℂ) + (Real.sin θ) • (Complex.I • P) := by
  letI : Algebra ℚ (Matrix I I ℂ) := Algebra.restrictScalars ℚ ℝ (Matrix I I ℂ)
  have hcont : Continuous (pauliHom P hP) := by
    have hfun : (⇑(pauliHom P hP) : ℂ → Matrix I I ℂ)
        = fun z => algebraMap ℝ (Matrix I I ℂ) z.re + z.im • (Complex.I • P) :=
      funext (pauliHom_apply P hP)
    rw [hfun]
    exact ((continuous_algebraMap ℝ (Matrix I I ℂ)).comp Complex.continuous_re).add
      (Complex.continuous_im.smul continuous_const)
  have hz : NormedSpace.exp ((θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I θ, Complex.ofReal_cos,
      Complex.ofReal_sin]
  have hmap := NormedSpace.map_exp (pauliHom P hP) hcont ((θ : ℂ) * Complex.I)
  rw [hz] at hmap
  have hB : pauliHom P hP ((θ : ℂ) * Complex.I) = θ • (Complex.I • P) := by
    rw [pauliHom_apply]
    simp
  have hC : pauliHom P hP ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
      (Real.cos θ) • (1 : Matrix I I ℂ) + (Real.sin θ) • (Complex.I • P) := by
    rw [pauliHom_apply]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Algebra.algebraMap_eq_smul_one]
  rw [hB, hC] at hmap
  exact hmap.symm

def rotation {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (θ : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-θ) • (Complex.I • P))

theorem rotation_eq_exp {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (θ : ℝ) :
    rotation P θ = NormedSpace.exp ((((-θ : ℝ) : ℂ) * Complex.I) • P) := by
  unfold rotation
  congr 1
  rw [← IsScalarTower.algebraMap_smul (A := ℂ) (M := Matrix I I ℂ) (-θ) (Complex.I • P),
    smul_smul]
  rfl

theorem rotation_euler {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ)
    (hP : P * P = 1) (θ : ℝ) :
    rotation P θ = (Real.cos θ) • (1 : Matrix I I ℂ) -
      (Real.sin θ) • (Complex.I • P) := by
  rw [rotation, exp_euler P hP (-θ), Real.cos_neg, Real.sin_neg, neg_smul,
    sub_eq_add_neg]

theorem rotation_unitary {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ)
    (hP : Pᴴ = P) (θ : ℝ) : rotation P θ ∈ Matrix.unitaryGroup I ℂ := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change ((-θ) • (Complex.I • P))ᴴ = -((-θ) • (Complex.I • P))
  simp [hP, Complex.conj_I]

theorem rotation_euler_complex {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ)
    (hP : P * P = 1) (θ : ℝ) :
    rotation P θ = (Real.cos θ : ℂ) • (1 : Matrix I I ℂ) +
      (-Complex.I * (Real.sin θ : ℂ)) • P := by
  rw [rotation_euler P hP θ]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
    smul_eq_mul]
  ring
