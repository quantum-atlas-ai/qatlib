/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Qatlib.Papers.QActiveLearn14.NativeReflect

@[expose] public section

/-!
# Operator separation of the two flag checks

[PaparoEtAl2014], Equation (8), flips flagged amplitudes, whereas Figure 2 and the proof
of Lemma 6 use the opposite check. Their matrices have operator-norm distance two on any
nonempty register. The sign is a global phase for the ideal finite word, as shown by
`Qatlib.Foundations.MatrixGeometry.FlagProjection.runFig_phase`.
-/

namespace Qatlib.Papers.QActiveLearn14.NativeReflect

open Qatlib.Foundations.MatrixGeometry.FlagProjection
open scoped Matrix.Norms.L2Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The diagonal matrix for Equation (8), with entries `-1` on flags and `1` elsewhere. -/
def equationCheckMatrix (S : Finset X) : Matrix X X ℂ :=
  Matrix.diagonal fun i => if i ∈ S then -1 else 1

/-- The matrix for Equation (8) acts by the literal flagged-coordinate sign flip. -/
theorem equation_check_matrix_apply (S : Finset X) (v : EuclideanSpace ℂ X) :
    Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (equationCheckMatrix S) v = check8 S v := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [Matrix.ofLp_toEuclideanCLM, equationCheckMatrix, Matrix.mulVec_diagonal]
  change (if i ∈ S then (-1 : ℂ) else 1) * v.ofLp i =
    v.ofLp i - 2 * (if i ∈ S then v.ofLp i else 0)
  split_ifs <;> ring

/-- The negative of the literal matrix is the Figure 2 check on the same Euclidean space. -/
theorem figure_check_matrix_apply (S : Finset X) (v : EuclideanSpace ℂ X) :
    Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (-equationCheckMatrix S) v = checkFig S v := by
  rw [map_neg, neg_apply, equation_check_matrix_apply, check_sign]

/-- On a nonempty register, the two checks have distance exactly two in the induced
`ℓ²` operator norm. -/
theorem check_sign_operator_distance [Nonempty X] (S : Finset X) :
    ‖equationCheckMatrix S - (-equationCheckMatrix S)‖ = 2 := by
  have hU : equationCheckMatrix S ∈ unitary (Matrix X X ℂ) := by
    rw [Unitary.mem_iff, equationCheckMatrix, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    constructor <;> rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] <;>
      congr 1 <;> funext i <;> by_cases hi : i ∈ S <;> simp [hi]
  rw [sub_neg_eq_add, ← two_smul ℂ, norm_smul, CStarRing.norm_of_mem_unitary hU, mul_one]
  norm_num

end Qatlib.Papers.QActiveLearn14.NativeReflect
