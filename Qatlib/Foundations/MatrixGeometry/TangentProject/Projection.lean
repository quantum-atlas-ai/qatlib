/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixGeometry.TangentProject
variable {n : Type*} [Fintype n] [DecidableEq n]

def realFrob (A B : Matrix n n ℂ) : ℝ := (Aᴴ * B).trace.re

def skew (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • (A - Aᴴ)

def herm (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • (A + Aᴴ)

def IsTangent (U V : Matrix n n ℂ) : Prop :=
  ∃ Ω : Matrix n n ℂ, Ωᴴ = -Ω ∧ V = Ω * U

def project (U Z : Matrix n n ℂ) : Matrix n n ℂ := skew (Z * Uᴴ) * U

omit [Fintype n] [DecidableEq n] in

theorem skew_adjoint (A : Matrix n n ℂ) : (skew A)ᴴ = -skew A := by
  simp only [skew, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]

omit [Fintype n] [DecidableEq n] in

theorem herm_adjoint (A : Matrix n n ℂ) : (herm A)ᴴ = herm A := by
  simp only [herm, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

omit [DecidableEq n] in

theorem project_tangent (U Z : Matrix n n ℂ) : IsTangent U (project U Z) :=
  ⟨skew (Z * Uᴴ), skew_adjoint _, rfl⟩

omit [DecidableEq n] in

theorem realFrob_herm_skew (H K : Matrix n n ℂ) (hH : Hᴴ = H) (hK : Kᴴ = -K) :
    realFrob H K = 0 := by
  have hc : star (H * K).trace = -(H * K).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH, hK,
      neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hr := congrArg Complex.re hc
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  simp only [realFrob, hH]
  linarith

theorem realFrob_mul_unitary (U A B : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    realFrob (A * U) (B * U) = realFrob A B := by
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  simp only [realFrob, Matrix.conjTranspose_mul]
  rw [show Uᴴ * Aᴴ * (B * U) = Uᴴ * (Aᴴ * B * U) by noncomm_ring,
    Matrix.trace_mul_comm Uᴴ, Matrix.mul_assoc (Aᴴ * B) U Uᴴ, hu, Matrix.mul_one]

theorem project_residual (U Z : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Z - project U Z = herm (Z * Uᴴ) * U := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hz : Z * Uᴴ * U = Z := by rw [Matrix.mul_assoc, hu, Matrix.mul_one]
  simp only [project, skew, herm, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul]
  rw [hz]
  module

theorem project_orthogonal (U Z V : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hV : IsTangent U V) : realFrob (Z - project U Z) V = 0 := by
  obtain ⟨Ω, hΩ, rfl⟩ := hV
  rw [project_residual U Z hU, realFrob_mul_unitary U _ _ hU]
  exact realFrob_herm_skew _ _ (herm_adjoint _) hΩ

theorem project_eq_self (U V : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hV : IsTangent U V) : project U V = V := by
  obtain ⟨Ω, hΩ, rfl⟩ := hV
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  simp only [project, Matrix.mul_assoc, hu, Matrix.mul_one, skew, hΩ, sub_neg_eq_add]
  congr 1
  module

omit [DecidableEq n] in

theorem realFrob_sub_left (A B C : Matrix n n ℂ) :
    realFrob (A - B) C = realFrob A C - realFrob B C := by
  simp only [realFrob, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
