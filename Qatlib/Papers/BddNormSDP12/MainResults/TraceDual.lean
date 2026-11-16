/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section


/-!
# Detecting spectral norm with trace-norm tests

Rank-one tests express Euclidean matrix coefficients as trace pairings. This
gives the spectral-norm half of trace/spectral duality without assuming any
duality theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators InnerProductSpace

namespace Qatlib.Papers.BddNormSDP12.MainResults.TraceDual

/-- Trace pairings against the trace-norm unit ball detect the spectral norm. -/
theorem opNorm_le_pair {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X : Matrix I I ℂ, Matrix.traceNorm X ≤ 1 →
      ‖Matrix.trace (Xᴴ * A)‖ ≤ C) : ‖A‖ ≤ C := by
  let T := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A
  change ‖T‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  have hx' : ∑ i, star (x i) * x i = (1 : ℂ) := by
    have hxx : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx]
      norm_num
    simpa only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply] using hxx
  have hy' : ∑ i, star (y i) * y i = (1 : ℂ) := by
    have hyy : ⟪y, y⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hy]
      norm_num
    simpa only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply] using hyy
  let X : Matrix I I ℂ := fun i j => y i * star (x j)
  have hX : Matrix.traceNorm X ≤ 1 := by
    exact (Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_unit_rank_one_traceNorm
      (fun i => y i) (fun i => x i) hy' hx').le
  have hp : Matrix.trace (Xᴴ * A) = ⟪y, T x⟫_ℂ := by
    change (∑ i, ∑ j, star (y j * star (x i)) * A j i) =
      ∑ j, (∑ i, A j i * x i) * star (y j)
    simp only [star_mul, star_star]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (⟪T x, y⟫_ℂ).re ≤ ‖⟪T x, y⟫_ℂ‖ := Complex.re_le_norm _
    _ = ‖⟪y, T x⟫_ℂ‖ := norm_inner_symm _ _
    _ = ‖Matrix.trace (Xᴴ * A)‖ := congrArg norm hp.symm
    _ ≤ C := h X hX

/-- A unitary matrix is a contraction, including the empty matrix space. -/
theorem unitary_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) : ‖(U : Matrix I I ℂ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty I
  · have hU : (U : Matrix I I ℂ) = 0 := Subsingleton.elim _ _
    simp [hU]
  · exact (CStarRing.norm_coe_unitary U).le

end Qatlib.Papers.BddNormSDP12.MainResults.TraceDual
