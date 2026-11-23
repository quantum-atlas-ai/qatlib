/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ContDiscWalk08.CompressedSim.CompressedSymbol

@[expose] public section

/-!
# A finite-dimensional operator-norm corollary of the compressed-walk estimate

This module advances [Childs2010], Section 3, eqs. (21)--(23). The public
scalar estimate is lifted to the genuine `ℓ₂` operator norm of a diagonal
Hamiltonian model. The bound is uniform in every diagonal eigenvalue and keeps
the constant outside the coordinate quantifier. See <https://arxiv.org/abs/0810.0312>.
-/
set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.CompressedSim

open Qatlib.Papers.ContDiscWalk08.CompressedSim

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar error symbol in the compressed-walk approximation. -/
def phaseError (lam t : ℝ) : ℂ :=
  compressedSymbol lam t - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))

/-- A coordinatewise bound lifts to the true `L2Operator` norm of a diagonal
operator.  The constant `B` is chosen before the universal coordinate premise. -/
theorem diagonal_phaseError_norm_le (lam : ι → ℝ) (t B : ℝ)
    (hB : 0 ≤ B)
    (hcoord : ∀ i, ‖phaseError (lam i) t‖ ≤ B) :
    ‖Matrix.diagonal (fun i => phaseError (lam i) t)‖ ≤ B := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hB).2 hcoord

/-- For a non-empty finite diagonal Hamiltonian model whose eigenvalues lie in
`[-1,1]`, the compressed-walk error is bounded in the Euclidean `ℓ₂` operator
norm by the uniform constant `1 + 2 |t|`. -/
theorem diagonal_phaseError_norm_le_uniform [Nonempty ι] (lam : ι → ℝ) (t : ℝ)
    (hLam : ∀ i, |lam i| ≤ 1) :
    ‖Matrix.diagonal (fun i => phaseError (lam i) t)‖ ≤ 1 + 2 * |t| := by
  apply diagonal_phaseError_norm_le lam t (1 + 2 * |t|)
  · positivity
  · intro i
    have hscalar := norm_compressedSymbol_sub_exp_neg_le_cubic (hLam i) t
    have hsq : (lam i) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (lam i)).2 (hLam i)
    have hfactor : 0 ≤ 1 + 2 * |t| * |lam i| := by positivity
    have hfactor_le : 1 + 2 * |t| * |lam i| ≤ 1 + 2 * |t| := by
      have hmul : 2 * |t| * |lam i| ≤ 2 * |t| * 1 := by
        exact mul_le_mul_of_nonneg_left (hLam i) (by positivity)
      linarith
    have hprod := mul_le_mul hsq hfactor_le hfactor (by norm_num : (0 : ℝ) ≤ 1)
    change ‖compressedSymbol (lam i) t
        - Complex.exp (-(Complex.I * ((t * lam i : ℝ) : ℂ)))‖ ≤ _
    exact hscalar.trans (by simpa using hprod)

end Qatlib.Papers.ContDiscWalk08.CompressedSim
