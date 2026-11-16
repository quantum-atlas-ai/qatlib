/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-!
# Gram-matrix identities for the affine minimum-norm problem

These are finite-dimensional algebraic identities used for Lemma 4.6 of
arXiv:2111.00405v1. No algorithmic cost or oracle abstraction is involved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators ComplexOrder
open Matrix
open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46

/-- The standard Hermitian inner product on a finite complex vector space. -/
def ip {n : ℕ} (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ y

/-- The Hermitian square is the squared Euclidean norm, as a complex number. -/
theorem ip_self {n : ℕ} (x : Fin n → ℂ) :
    ip x x = (l2NormSq x : ℂ) := by
  simp only [ip, dotProduct, l2NormSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [← Complex.normSq_eq_norm_sq, Complex.mul_conj, mul_comm]

/-- Moving a matrix across an inner product conjugates and transposes it. -/
theorem ip_mulVec {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ)
    (x : Fin n → ℂ) (y : Fin k → ℂ) :
    ip x (A *ᵥ y) = ip (Aᴴ *ᵥ x) y := by
  simp only [ip, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

/-- The quadratic form of a Gram matrix is the squared image norm. -/
theorem ip_gram {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (x y : Fin k → ℂ) :
    ip x ((Vᴴ * V) *ᵥ y) = ip (V *ᵥ x) (V *ᵥ y) := by
  rw [← mulVec_mulVec, ip_mulVec]
  simp

/-- The Gram matrix and the original matrix have the same kernel. -/
theorem gram_zero_iff {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (x : Fin k → ℂ) : (Vᴴ * V) *ᵥ x = 0 ↔ V *ᵥ x = 0 := by
  constructor
  · intro h
    apply dotProduct_star_self_eq_zero.mp
    change ip (V *ᵥ x) (V *ᵥ x) = 0
    rw [← ip_gram, h]
    simp [ip]
  · intro h
    rw [← mulVec_mulVec, h, mulVec_zero]

/-- The complex Cauchy-Schwarz inequality in the paper's norm notation. -/
theorem ip_norm_sq_le {n : ℕ} (x y : Fin n → ℂ) :
    ‖ip x y‖ ^ 2 ≤ l2NormSq x * l2NormSq y := by
  have hnorm : ‖ip x y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    calc
      ‖ip x y‖ = ‖∑ i, star (x i) * y i‖ := rfl
      _ ≤ ∑ i, ‖star (x i) * y i‖ :=
        norm_sum_le Finset.univ (fun i : Fin n => star (x i) * y i)
      _ = ∑ i, ‖x i‖ * ‖y i‖ := by simp
  have hnon : 0 ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq := (sq_le_sq₀ (norm_nonneg _) hnon).mpr hnorm
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖x i‖) (fun i => ‖y i‖))

/-- Solvable vector equations are solved by the matrix pseudoinverse. -/
theorem pinv_solves {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ)
    (b : Fin k → ℂ) (hb : ∃ x, G *ᵥ x = b) :
    G *ᵥ (matrixPseudoinverse G *ᵥ b) = b := by
  obtain ⟨x, rfl⟩ := hb
  rw [mulVec_mulVec, mulVec_mulVec, mul_matrixPseudoinverse_mul]

/-- An inner product with the all-ones vector is the coordinate sum. -/
theorem ip_one {k : ℕ} (x : Fin k → ℂ) :
    ip (fun _ => 1) x = ∑ i, x i := by
  simp [ip, dotProduct]

/-- Reversing the arguments conjugates the Hermitian inner product. -/
theorem ip_swap {k : ℕ} (x y : Fin k → ℂ) : ip x y = star (ip y x) :=
  star_dotProduct x y

/-- Subtracting a real all-ones rank-one matrix subtracts a squared coordinate sum. -/
theorem gram_rank_one {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (γ : ℝ) (z : Fin k → ℂ) :
    (ip z (((Vᴴ * V) - γ • Matrix.of (fun _ _ => (1 : ℂ))) *ᵥ z)).re =
      l2NormSq (V *ᵥ z) - γ * ‖∑ i, z i‖ ^ 2 := by
  rw [Matrix.sub_mulVec, ip, dotProduct_sub, Complex.sub_re]
  congr 1
  · exact congrArg Complex.re (ip_gram V z z |>.trans (ip_self _))
  · simp only [Matrix.smul_mulVec, dotProduct_smul]
    have h : Matrix.of (fun _ _ : Fin k => (1 : ℂ)) *ᵥ z =
        (∑ i, z i) • (fun _ => (1 : ℂ)) := by
      ext i
      simp [mulVec, dotProduct]
    rw [h, dotProduct_smul]
    have hs : star z ⬝ᵥ (fun _ => (1 : ℂ)) = star (∑ i, z i) := by
      simp [dotProduct, star_sum]
    rw [hs]
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, mul_comm]

/-- A Gram equation with all-ones right-hand side evaluates every affine coordinate sum. -/
theorem gram_ip_left {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    {u : Fin k → ℂ} (hu : (Vᴴ * V) *ᵥ u = fun _ => 1)
    (z : Fin k → ℂ) : ip (V *ᵥ u) (V *ᵥ z) = ∑ i, z i := by
  rw [← ip_gram, ip_mulVec]
  simpa [hu] using ip_one z

/-- The coordinate sum of a solution of the Gram equation is a real squared norm. -/
theorem gram_sum_real {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    {u : Fin k → ℂ} (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) :
    (∑ i, u i) = (l2NormSq (V *ᵥ u) : ℂ) :=
  (gram_ip_left V hu u).symm.trans (ip_self _)

/-- The Gram-equation image has positive squared norm when there is at least one column. -/
theorem gram_image_pos {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) {u : Fin k → ℂ}
    (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) : 0 < l2NormSq (V *ᵥ u) := by
  refine lt_of_le_of_ne (l2NormSq_nonneg _) ?_
  intro h
  have hz : V *ᵥ u = 0 := by
    apply dotProduct_star_self_eq_zero.mp
    change ip (V *ᵥ u) (V *ᵥ u) = 0
    rw [ip_self, ← h]
    rfl
  have he := (gram_zero_iff V u).mpr hz
  rw [hu] at he
  have hi := congrFun he ⟨0, hk⟩
  norm_num at hi

/-- Squared Euclidean norm is homogeneous with the squared complex scalar norm. -/
theorem l2sq_smul {k : ℕ} (c : ℂ) (z : Fin k → ℂ) :
    l2NormSq (c • z) = ‖c‖ ^ 2 * l2NormSq z := by
  simp [l2NormSq, mul_pow, Finset.mul_sum]

/-- A normalized Gram-equation solution has unit coordinate sum. -/
theorem gram_normal_sum {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) {u : Fin k → ℂ}
    (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) :
    (∑ i, (((l2NormSq (V *ᵥ u))⁻¹ : ℝ) : ℂ) * u i) = 1 := by
  rw [← Finset.mul_sum, gram_sum_real V hu, ← Complex.ofReal_mul]
  simp [ne_of_gt (gram_image_pos hk V hu)]

/-- The normalized Gram-equation solution attains the reciprocal squared norm. -/
theorem gram_normal_norm {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) {u : Fin k → ℂ}
    (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) :
    l2NormSq (V *ᵥ ((((l2NormSq (V *ᵥ u))⁻¹ : ℝ) : ℂ) • u)) =
      (l2NormSq (V *ᵥ u))⁻¹ := by
  rw [Matrix.mulVec_smul, l2sq_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
    (l2NormSq_nonneg (V *ᵥ u)))]
  field_simp [ne_of_gt (gram_image_pos hk V hu)]

/-- Cauchy-Schwarz gives the rank-one lower bound from the Gram equation. -/
theorem gram_rank_bound {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) {u : Fin k → ℂ}
    (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) (z : Fin k → ℂ) :
    (l2NormSq (V *ᵥ u))⁻¹ * ‖∑ i, z i‖ ^ 2 ≤ l2NormSq (V *ᵥ z) := by
  have h := ip_norm_sq_le (V *ᵥ u) (V *ᵥ z)
  rw [gram_ip_left V hu z] at h
  apply (mul_le_mul_iff_right₀ (gram_image_pos hk V hu)).mp
  calc
    l2NormSq (V *ᵥ u) * ((l2NormSq (V *ᵥ u))⁻¹ * ‖∑ i, z i‖ ^ 2) =
        ‖∑ i, z i‖ ^ 2 := by
      field_simp [ne_of_gt (gram_image_pos hk V hu)]
    _ ≤ l2NormSq (V *ᵥ u) * l2NormSq (V *ᵥ z) := h

/-- The paper's positive-semidefinite order, expressed by nonnegative quadratic forms. -/
def devPSD {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ z : Fin m → ℂ, 0 ≤ (star z ⬝ᵥ (A *ᵥ z)).re

/-- An affine combination equal to zero forces the optimal rank-one subtraction to be zero. -/
theorem gram_zero_opt {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    {x : Fin k → ℂ} (hs : (∑ i, x i) = 1) (hx : V *ᵥ x = 0) :
    devPSD (Vᴴ * V) ∧
      ∀ γ : ℝ, devPSD ((Vᴴ * V) - γ • Matrix.of (fun _ _ => (1 : ℂ))) → γ ≤ 0 := by
  constructor
  · intro z
    change 0 ≤ (ip z ((Vᴴ * V) *ᵥ z)).re
    rw [ip_gram, ip_self]
    exact l2NormSq_nonneg (V *ᵥ z)
  · intro γ hγ
    have h := hγ x
    change 0 ≤ (ip x (((Vᴴ * V) - γ • Matrix.of (fun _ _ => (1 : ℂ))) *ᵥ x)).re at h
    rw [gram_rank_one, hx, hs] at h
    simpa [l2NormSq] using h

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
