/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
public import Qatlib.Papers.SparseNetwork13.MainResults.Model.SpectralModel

/-!
# Quadratic forms of electrical-network Laplacians

For [Wang2017Networks], Equations (6), (89) and (98), the incidence factorization identifies
the combinatorial quadratic form with the sum of conductance-weighted squared voltage drops.
The extra column in the augmented network adds a nonnegative square for a nonnegative weight.
-/

public section

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.SparseNetwork13.MainResults.Spectral

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The combinatorial Laplacian quadratic form is the sum of weighted squared voltage drops. -/
theorem laplacian_quadratic_eq (G : ElecNetwork V E) (x : V → ℝ) :
    x ⬝ᵥ (laplacian G *ᵥ x) = ∑ e, G.w e * (x (G.tail e) - x (G.head e)) ^ 2 := by
  rw [laplacian, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose, weightMatrix]
  simp only [dotProduct, mulVec_diagonal, incident_transpose_mulVec_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The incidence factorization expresses the Laplacian energy as a squared Euclidean norm. -/
theorem laplacian_quadratic_eq_norm_sq (G : ElecNetwork V E) (x : EuclideanSpace ℝ V) :
    x.ofLp ⬝ᵥ (laplacian G *ᵥ x.ofLp) =
      ‖(WithLp.toLp 2 fun e => Real.sqrt (G.w e) * (x (G.tail e) - x (G.head e)) :
        EuclideanSpace ℝ E)‖ ^ 2 := by
  rw [laplacian_quadratic_eq, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun e _ => ?_
  change G.w e * (x (G.tail e) - x (G.head e)) ^ 2 =
    (Real.sqrt (G.w e) * (x (G.tail e) - x (G.head e))) ^ 2
  rw [mul_pow, Real.sq_sqrt (G.w_pos e).le]

/-- Adding a constant potential leaves the combinatorial Laplacian quadratic form unchanged. -/
theorem laplacian_quadratic_sub_const (G : ElecNetwork V E) (x : V → ℝ) (c : ℝ) :
    (fun v => x v - c) ⬝ᵥ (laplacian G *ᵥ (fun v => x v - c)) =
      x ⬝ᵥ (laplacian G *ᵥ x) := by
  simp only [laplacian_quadratic_eq, sub_sub_sub_cancel_right]

omit [DecidableEq V] in
/-- The added rank-one matrix scales the current by its pairing with the input. -/
private theorem special_edge_mulVec (lam : ℝ) (x current : V → ℝ) :
    (Matrix.of (fun u v => 2 * lam * (current u * current v)) *ᵥ x) =
      (2 * lam * (current ⬝ᵥ x)) • current := by
  funext u
  simp only [mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_right_comm (2 * lam) _ (current u), Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The Laplacian of the augmented network adds the squared pairing with the extra column. -/
theorem modified_laplacian_quadratic_eq (G : ElecNetwork V E) (lam : ℝ) (x current : V → ℝ) :
    x ⬝ᵥ (modifiedLaplacian G lam current *ᵥ x) =
      x ⬝ᵥ (laplacian G *ᵥ x) + 2 * lam * (current ⬝ᵥ x) ^ 2 := by
  rw [modifiedLaplacian, add_mulVec, special_edge_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_comm x current, smul_eq_mul, pow_two]
  ring

/-- The added term from [Wang2017Networks], Equation (89), has L2 operator norm
`2 * lam * ‖current‖ ^ 2`. A unit external current therefore gives an update of norm
`2 * lam` independently of the dimension. -/
theorem modified_laplacian_sub_norm (G : ElecNetwork V E) {lam : ℝ} (hlam : 0 ≤ lam)
    (current : EuclideanSpace ℝ V) :
    ‖modifiedLaplacian G lam current.ofLp - laplacian G‖ = 2 * lam * ‖current‖ ^ 2 := by
  let A : Matrix V V ℝ := Matrix.of fun u v => 2 * lam * (current u * current v)
  have hA : modifiedLaplacian G lam current.ofLp - laplacian G = A := by
    change laplacian G + A - laplacian G = A
    exact add_sub_cancel_left _ _
  have hCLM : Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) A =
      (2 * lam) • InnerProductSpace.rankOne ℝ current current := by
    ext1 x
    apply WithLp.ofLp_injective 2
    change A *ᵥ x.ofLp = _
    rw [special_edge_mulVec]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, smul_smul]
  rw [hA, ← Matrix.l2_opNorm_toEuclideanCLM, hCLM, norm_smul, InnerProductSpace.norm_rankOne,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg zero_le_two hlam), pow_two]

/-- A balanced external current preserves the constant null vector of the combinatorial
Laplacian after augmentation. -/
theorem modified_laplacian_mulVec_one (G : ElecNetwork V E) (lam : ℝ) (current : V → ℝ)
    (hbalance : ∑ v, current v = 0) :
    modifiedLaplacian G lam current *ᵥ (fun _ => 1) = 0 := by
  have hinc : (incident G)ᵀ *ᵥ (fun _ => 1) = 0 := by
    funext e
    rw [incident_transpose_mulVec_apply]
    simp
  have hdot : current ⬝ᵥ (fun _ => 1) = 0 := by simpa [dotProduct] using hbalance
  rw [modifiedLaplacian, add_mulVec, special_edge_mulVec, hdot, mul_zero, zero_smul, add_zero,
    laplacian, ← mulVec_mulVec, hinc, mulVec_zero]

end Qatlib.Papers.SparseNetwork13.MainResults.Spectral
