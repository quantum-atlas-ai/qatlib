/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Qatlib.Papers.RydbergMaxCut26.Resources.DipolarDefs

@[expose] public section

/-!
# A finite Rydberg exchange operator

The static term of [CrostaSaubanereHuber2026], Equation (8), assigns a real coefficient to
each distinct pair of sites. The matrix `rydbergExchange` collects those coefficients on
the site space with zero diagonal. A single nonnegative envelope `C` on the pair couplings
bounds its Euclidean `L2Operator` norm. A positive lower bound on the inter-site distance
supplies such an envelope for the dipolar coefficients of the source.

The estimate concerns the site coefficient matrix. Bounds on the many-body Pauli Hamiltonian
and guarantees for annealing or geometric realization are outside its scope.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026] ([arXiv:2606.27224v1](https://arxiv.org/abs/2606.27224v1))
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.RydbergMaxCut26.Resources

variable {n : ℕ}

/-- The site matrix of exchange coefficients, with the self-loop entries removed. -/
def rydbergExchange (J : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then 0 else (J i j : ℂ)

/-- A positive site count supplies a genuinely nonempty Euclidean site space. -/
theorem rydbergExchange_nonempty (n : ℕ) (hn : 0 < n) : Nonempty (Fin n) :=
  ⟨⟨0, hn⟩⟩

/-- A symmetric real coupling produces a Hermitian exchange matrix. -/
theorem rydbergExchange_isHermitian (J : Fin n → Fin n → ℝ)
    (hJ : ∀ i j, J i j = J j i) : (rydbergExchange J).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [rydbergExchange]
  · have hji : ¬j = i := Ne.symm hij
    simp [rydbergExchange, hij, hji, hJ]

/-- Weighted Cauchy--Schwarz for the finite row estimate. -/
private theorem sq_sum_mul_le_sum_mul_sum_sq {α : Type*} (s : Finset α)
    (a b : α → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, a i * (b i) ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha (fun i hi => ?_) (fun i hi => ?_)
  · exact mul_nonneg (ha i hi) (sq_nonneg _)
  · rw [show (a i * b i) ^ 2 = a i * (a i * (b i) ^ 2) by ring]

/-- Each output coordinate is controlled by its absolute row sum. -/
private theorem mulVec_normSq_le (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (i : Fin n) :
    ‖(A *ᵥ v) i‖ ^ 2 ≤
      (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖v j‖ ^ 2) := by
  have hcoord : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    calc
      ‖(A *ᵥ v) i‖ = ‖∑ j, A i j * v j‖ := by rfl
      _ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A i j‖ * ‖v j‖ := by
        exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  have hsum : 0 ≤ ∑ j, ‖A i j‖ * ‖v j‖ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum).mpr hcoord
  refine hsq.trans ?_
  simpa using sq_sum_mul_le_sum_mul_sum_sq
    (Finset.univ : Finset (Fin n)) (fun j => ‖A i j‖) (fun j => ‖v j‖)
    (fun _ _ => norm_nonneg _)

/-- A nonnegative uniform bound on the Euclidean action of every vector bounds the matrix's
`L2Operator` norm. -/
private theorem l2_opNorm_le_of_mulVec_le (A : Matrix (Fin n) (Fin n) ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ v : Fin n → ℂ,
      ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ C * ‖WithLp.toLp 2 v‖) : ‖A‖ ≤ C := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro x
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp]
  exact h x.ofLp

/-- The Schur estimate for a finite matrix with a common row and column bound. -/
private theorem norm_le_of_rowSum_colSum_le (A : Matrix (Fin n) (Fin n) ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ C)
    (hcol : ∀ j, (∑ i, ‖A i j‖) ≤ C) : ‖A‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec_le A hC (fun v => ?_)
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp ?_
  calc
    ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 = ∑ i, ‖(A *ᵥ v) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ i, (∑ j, ‖A i j‖) * (∑ j, ‖A i j‖ * ‖v j‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => mulVec_normSq_le A v i
    _ ≤ ∑ i, C * (∑ j, ‖A i j‖ * ‖v j‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg fun j _ => by positivity)
    _ = C * ∑ i, ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ j, (∑ i, ‖A i j‖) * ‖v j‖ ^ 2 := by
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul ..).symm
    _ ≤ C * ∑ j, C * ‖v j‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hC
      exact mul_le_mul_of_nonneg_right (hcol j) (by positivity)
    _ = C ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = (C * ‖WithLp.toLp 2 v‖) ^ 2 := by
      rw [mul_pow, EuclideanSpace.norm_sq_eq]

/-- A uniform coupling envelope gives a true Euclidean operator-norm bound for the exchange
matrix.  The site space is nonempty through `hn`, and the same constant `C` controls every
off-diagonal pair. -/
theorem rydbergExchange_l2Operator_norm_le (n : ℕ) (hn : 0 < n) (J : Fin n → Fin n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ i j, i ≠ j → |J i j| ≤ C) :
    ‖rydbergExchange J‖ ≤ (n : ℝ) * C := by
  let A := rydbergExchange J
  have hentry (i j : Fin n) : ‖A i j‖ ≤ C := by
    by_cases hij : i = j
    · subst hij
      simp [A, rydbergExchange, hC]
    · rw [show A i j = (J i j : ℂ) by simp [A, rydbergExchange, hij]]
      simpa [Complex.norm_real, Real.norm_eq_abs] using hJ i j hij
  have hsum (i : Fin n) : (∑ j, ‖A i j‖) ≤ (n : ℝ) * C := by
    calc
      (∑ j, ‖A i j‖) ≤ ∑ _j : Fin n, C :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = (n : ℝ) * C := by simp
  apply norm_le_of_rowSum_colSum_le A (mul_nonneg (by positivity) hC) hsum
  intro j
  calc
    (∑ i, ‖A i j‖) ≤ ∑ _i : Fin n, C :=
      Finset.sum_le_sum fun i _ => hentry i j
    _ = (n : ℝ) * C := by simp

/-- A positive inter-site separation bounds the norm of the site coefficient matrix
for the dipolar couplings of [CrostaSaubanereHuber2026], Equation (8). -/
theorem rydbergDipolar_l2Operator_norm_le (n : ℕ) (hn : 1 < n) (C3 : ℝ)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (position i) (position j)) :
    ‖rydbergExchange (Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar.coupling C3 position)‖ ≤
      (n : ℝ) * (|C3| / (2 * δ ^ 3)) := by
  refine rydbergExchange_l2Operator_norm_le n (by omega) _ (|C3| / (2 * δ ^ 3))
    (by positivity) ?_
  intro i j hij
  have hd := hsep i j hij
  rw [Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar.coupling, abs_div,
    abs_of_nonneg (show 0 ≤ 2 * dist (position i) (position j) ^ 3 by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg C3) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hd 3) (by norm_num))

end Qatlib.Papers.RydbergMaxCut26.Resources
