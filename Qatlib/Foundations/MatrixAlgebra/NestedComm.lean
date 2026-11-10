/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Matrix
namespace Qatlib.Foundations.MatrixAlgebra.NestedComm
noncomputable section

def comm {A : Type*} [Mul A] [Sub A] (X Y : A) : A := X * Y - Y * X

def nested {A : Type*} [Mul A] [Sub A] (X Y Z : A) : A := comm X (comm Y Z)

theorem comm_norm_le {A : Type*} [NormedRing A] (X Y : A) :
    ‖comm X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc ‖comm X Y‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
       _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
       _ = 2 * ‖X‖ * ‖Y‖ := by ring

theorem nested_norm_le {A : Type*} [NormedRing A] (X Y Z : A) :
    ‖nested X Y Z‖ ≤ 4 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  calc ‖nested X Y Z‖ ≤ 2 * ‖X‖ * ‖comm Y Z‖ := comm_norm_le _ _
       _ ≤ 2 * ‖X‖ * (2 * ‖Y‖ * ‖Z‖) :=
         mul_le_mul_of_nonneg_left (comm_norm_le _ _) (by positivity)
       _ = 4 * ‖X‖ * ‖Y‖ * ‖Z‖ := by ring

variable {D : Type*} [Fintype D]

theorem trace_comm (X Y : Matrix D D ℂ) : (comm X Y).trace = 0 := by
  simp only [comm, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]

theorem trace_nested (X Y Z : Matrix D D ℂ) : (nested X Y Z).trace = 0 := trace_comm _ _

theorem nested_hermitian (X Y Z : Matrix D D ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hZ : Z.IsHermitian) :
    (nested X Y Z).IsHermitian := by
  change (nested X Y Z)ᴴ = nested X Y Z
  simp only [nested, comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hX.eq, hY.eq, hZ.eq]
  noncomm_ring

variable [DecidableEq D]

def opNorm (M : Matrix D D ℂ) : ℝ := ‖(Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) M‖

theorem nested_opNorm_le (X Y Z : Matrix D D ℂ) :
    opNorm (nested X Y Z) ≤ 4 * opNorm X * opNorm Y * opNorm Z := by
  unfold opNorm
  simpa only [nested, comm, map_sub, map_mul] using
    nested_norm_le ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) X) ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) Y) ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) Z)

end
end Qatlib.Foundations.MatrixAlgebra.NestedComm
