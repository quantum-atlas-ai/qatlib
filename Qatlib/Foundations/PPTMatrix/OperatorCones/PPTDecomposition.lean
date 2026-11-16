/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.PPTDecompositionSVD
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse

@[expose] public section




/-!
# Simultaneous rank-one decomposition of a PPT pair of block matrices

If both `fromBlocks A B Bᴴ C` and its partial transpose `fromBlocks A Bᴴ B C` are positive
semidefinite, then there are vectors `u k`, `v k`, real numbers `lam k` and a positive
semidefinite remainder `R` with

* `C = ∑ k, (u k (u k)ᴴ + v k (v k)ᴴ)`,
* `B = ∑ k, 2 * lam k • u k (v k)ᴴ`,
* `A = R + ∑ k, lam k ^ 2 • (u k (u k)ᴴ + v k (v k)ᴴ)`

(`exists_ppt_decomposition`). The public decomposition uses the SVD on `Ran(C)`,
its prescribed square-root vectors, and the explicit positive Schur remainder.
The Hermitian-dilation resolution below is retained as an independent reusable construction.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-! ### Scalar identities -/

/-- Establishes `ofReal_half`: `((1 / 2 : ℝ) : ℂ) = 1 / 2`, for the stated parameters. -/
private theorem ofReal_half : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num

/-- Establishes `ofReal_two`: `((2 : ℝ) : ℂ) = 2`, for the stated parameters. -/
private theorem ofReal_two : ((2 : ℝ) : ℂ) = 2 := by norm_num

/-- Establishes `real_half_sqrt_mul_self`: `Real.sqrt (x / 2) * Real.sqrt (x / 2) = 1 / 2 * x`, for the stated parameters. -/
private theorem real_half_sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x / 2) * Real.sqrt (x / 2) = 1 / 2 * x := by
  rw [Real.mul_self_sqrt (div_nonneg hx zero_le_two)]
  ring

/-- Establishes `real_half_sqrt_mul_inv`: `Real.sqrt (x / 2) * (Real.sqrt (x / 2))⁻¹ = x * x⁻¹`, for the stated parameters. -/
private theorem real_half_sqrt_mul_inv {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x / 2) * (Real.sqrt (x / 2))⁻¹ = x * x⁻¹ := by
  by_cases h0 : x = 0
  · simp [h0]
  · rw [mul_inv_cancel₀ ((Real.sqrt_ne_zero (div_nonneg hx zero_le_two)).mpr
      (div_ne_zero h0 two_ne_zero)), mul_inv_cancel₀ h0]

/-- Establishes `real_half_inv_mul_sqrt`: `(Real.sqrt (x / 2))⁻¹ * Real.sqrt (x / 2) = x * x⁻¹`, for the stated parameters. -/
private theorem real_half_inv_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (x / 2))⁻¹ * Real.sqrt (x / 2) = x * x⁻¹ := by
  rw [mul_comm (Real.sqrt (x / 2))⁻¹ (Real.sqrt (x / 2)), real_half_sqrt_mul_inv hx]

/-- Establishes `real_half_inv_sqrt_mul_self`: `(Real.sqrt (x / 2))⁻¹ * (Real.sqrt (x / 2))⁻¹ = 2 * x⁻¹`, for the stated parameters. -/
private theorem real_half_inv_sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (x / 2))⁻¹ * (Real.sqrt (x / 2))⁻¹ = 2 * x⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (div_nonneg hx zero_le_two), inv_div, div_eq_mul_inv]

/-! ### Small matrix identities -/

/-- Establishes `half_add_half`: `(1 / 2 : ℂ) • M + (1 / 2 : ℂ) • M = M`, for the stated parameters. -/
private theorem half_add_half {n : Type*} (M : Matrix n n ℂ) :
    (1 / 2 : ℂ) • M + (1 / 2 : ℂ) • M = M := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Establishes `half_identity`: `A = ((1 / 2 : ℝ) : ℂ) • ((A - X) + (A - Y)) + (1 / 4 : ℂ) • ((2 : ℂ) • X + (2 : ℂ) • Y)`, for the stated parameters. -/
private theorem half_identity {n : Type*} (A X Y : Matrix n n ℂ) :
    A = ((1 / 2 : ℝ) : ℂ) • ((A - X) + (A - Y)) +
      (1 / 4 : ℂ) • ((2 : ℂ) • X + (2 : ℂ) • Y) := by
  rw [ofReal_half]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Establishes `mul_smul_add_split`: `(c * d) • (U + V) = c • (d • U) + c • (d • V)`, for the stated parameters. -/
private theorem mul_smul_add_split {n : Type*} (c d : ℂ) (U V : Matrix n n ℂ) :
    (c * d) • (U + V) = c • (d • U) + c • (d • V) := by
  rw [smul_add, mul_smul, mul_smul]

/-- Establishes `posSemidef_half_smul`: `(((1 / 2 : ℝ) : ℂ) • M).PosSemidef`, for the stated parameters. -/
private theorem posSemidef_half_smul {n : Type*} {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : (((1 / 2 : ℝ) : ℂ) • M).PosSemidef :=
  hM.smul (Complex.zero_le_real.mpr (by norm_num))

/-- Conjugating a rank-one matrix `a bᴴ` by `M` gives `(M a) (M b)ᴴ`. -/
private theorem vecMulVec_mulVec_star_mulVec {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (a b : n → ℂ) :
    vecMulVec (M *ᵥ a) (star (M *ᵥ b)) = M * vecMulVec a (star b) * Mᴴ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- Establishes `sum_conj`: `∑ k, vecMulVec (G *ᵥ a k) (star (G *ᵥ b k)) = G * (∑ k, vecMulVec (a k) (star (b k))) * G`, for the stated parameters. -/
private theorem sum_conj {ι n : Type*} [Fintype ι] [Fintype n] (G : Matrix n n ℂ)
    (hG : Gᴴ = G) (a b : ι → n → ℂ) :
    ∑ k, vecMulVec (G *ᵥ a k) (star (G *ᵥ b k)) =
      G * (∑ k, vecMulVec (a k) (star (b k))) * G := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vecMulVec_mulVec_star_mulVec, hG]

/-- Establishes `sum_smul_conj`: `∑ k, c k • vecMulVec (G *ᵥ a k) (star (G *ᵥ b k)) = G * (∑ k, c k • vecMulVec (a k) (star (b k))) * G`, for the stated parameters. -/
private theorem sum_smul_conj {ι n : Type*} [Fintype ι] [Fintype n] (G : Matrix n n ℂ)
    (hG : Gᴴ = G) (c : ι → ℂ) (a b : ι → n → ℂ) :
    ∑ k, c k • vecMulVec (G *ᵥ a k) (star (G *ᵥ b k)) =
      G * (∑ k, c k • vecMulVec (a k) (star (b k))) * G := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vecMulVec_mulVec_star_mulVec, hG, Matrix.mul_smul, Matrix.smul_mul]

/-! ### Square roots of `C / 2` and of its pseudo-inverse -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n ℂ}

/-- The spectral calculus is homogeneous in the function. -/
private theorem cfc_const_mul (hC : C.IsHermitian) (r : ℝ) (f : ℝ → ℝ) :
    hC.cfc (fun x => r * f x) = (r : ℂ) • hC.cfc f := by
  have hfun : (fun i => ((r * f (hC.eigenvalues i) : ℝ) : ℂ)) =
      (r : ℂ) • (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  calc hC.cfc (fun x => r * f x)
      = (hC.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (fun i => ((r * f (hC.eigenvalues i) : ℝ) : ℂ)) *
          star (hC.eigenvectorUnitary : Matrix n n ℂ) := cfc_eq_mul hC (fun x => r * f x)
    _ = (hC.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal ((r : ℂ) • (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ))) *
          star (hC.eigenvectorUnitary : Matrix n n ℂ) := by rw [hfun]
    _ = (r : ℂ) • ((hC.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) *
          star (hC.eigenvectorUnitary : Matrix n n ℂ)) := by
        rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    _ = (r : ℂ) • hC.cfc f := by rw [cfc_eq_mul hC f]

/-- For positive semidefinite `C` there are Hermitian `G` (the square root of `C / 2`) and `Gi`
(the square root of the pseudo-inverse of `C / 2`) with `G * G = C / 2`,
`G * Gi = Gi * G = C * pinv C` and `Gi * Gi = 2 • pinv C`. -/
private theorem exists_half_sqrt (hC : C.PosSemidef) :
    ∃ G Gi : Matrix n n ℂ, Gᴴ = G ∧ Giᴴ = Gi ∧ G * G = (1 / 2 : ℂ) • C ∧
      G * Gi = C * pinv C ∧ Gi * G = C * pinv C ∧ Gi * Gi = (2 : ℂ) • pinv C := by
  have hH : C.IsHermitian := hC.isHermitian
  refine ⟨hH.cfc (fun x => Real.sqrt (x / 2)), hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹),
    (isHermitian_cfc hH _).eq, (isHermitian_cfc hH _).eq, ?_, ?_, ?_, ?_⟩
  · calc hH.cfc (fun x => Real.sqrt (x / 2)) * hH.cfc (fun x => Real.sqrt (x / 2))
        = hH.cfc (fun x => Real.sqrt (x / 2) * Real.sqrt (x / 2)) :=
          cfc_mul_cfc hH (fun x => Real.sqrt (x / 2)) (fun x => Real.sqrt (x / 2))
      _ = hH.cfc (fun x => (1 / 2 : ℝ) * x) :=
          cfc_congr_eigenvalues hH (f := fun x => Real.sqrt (x / 2) * Real.sqrt (x / 2))
            (g := fun x => (1 / 2 : ℝ) * x)
            (fun i => real_half_sqrt_mul_self (hC.eigenvalues_nonneg i))
      _ = ((1 / 2 : ℝ) : ℂ) • hH.cfc (fun x => x) := cfc_const_mul hH (1 / 2) (fun x => x)
      _ = (1 / 2 : ℂ) • C := by rw [cfc_id hH, ofReal_half]
  · calc hH.cfc (fun x => Real.sqrt (x / 2)) * hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹)
        = hH.cfc (fun x => Real.sqrt (x / 2) * (Real.sqrt (x / 2))⁻¹) :=
          cfc_mul_cfc hH (fun x => Real.sqrt (x / 2)) (fun x => (Real.sqrt (x / 2))⁻¹)
      _ = hH.cfc (fun x => x * x⁻¹) :=
          cfc_congr_eigenvalues hH (f := fun x => Real.sqrt (x / 2) * (Real.sqrt (x / 2))⁻¹)
            (g := fun x => x * x⁻¹)
            (fun i => real_half_sqrt_mul_inv (hC.eigenvalues_nonneg i))
      _ = C * pinv C := (mul_pinv_eq_cfc hH).symm
  · calc hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹) * hH.cfc (fun x => Real.sqrt (x / 2))
        = hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹ * Real.sqrt (x / 2)) :=
          cfc_mul_cfc hH (fun x => (Real.sqrt (x / 2))⁻¹) (fun x => Real.sqrt (x / 2))
      _ = hH.cfc (fun x => x * x⁻¹) :=
          cfc_congr_eigenvalues hH (f := fun x => (Real.sqrt (x / 2))⁻¹ * Real.sqrt (x / 2))
            (g := fun x => x * x⁻¹)
            (fun i => real_half_inv_mul_sqrt (hC.eigenvalues_nonneg i))
      _ = C * pinv C := (mul_pinv_eq_cfc hH).symm
  · calc hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹) * hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹)
        = hH.cfc (fun x => (Real.sqrt (x / 2))⁻¹ * (Real.sqrt (x / 2))⁻¹) :=
          cfc_mul_cfc hH (fun x => (Real.sqrt (x / 2))⁻¹) (fun x => (Real.sqrt (x / 2))⁻¹)
      _ = hH.cfc (fun x => (2 : ℝ) * x⁻¹) :=
          cfc_congr_eigenvalues hH
            (f := fun x => (Real.sqrt (x / 2))⁻¹ * (Real.sqrt (x / 2))⁻¹)
            (g := fun x => (2 : ℝ) * x⁻¹)
            (fun i => real_half_inv_sqrt_mul_self (hC.eigenvalues_nonneg i))
      _ = ((2 : ℝ) : ℂ) • hH.cfc (fun x => x⁻¹) := cfc_const_mul hH 2 (fun x => x⁻¹)
      _ = (2 : ℂ) • pinv C := by rw [← pinv_eq_cfc hH, ofReal_two]

end Spectral

/-! ### Spectral resolution of a Hermitian dilation, read off blockwise -/

/-- Establishes `sum_vecMulVec_eq`: `∑ k, vecMulVec (fun a => W (f a) k) (star (fun a => W (g a) k)) = (W * star W).submatrix f g`, for the stated parameters. -/
private theorem sum_vecMulVec_eq {m n : Type*} [Fintype m] (W : Matrix m m ℂ) (f g : n → m) :
    ∑ k, vecMulVec (fun a => W (f a) k) (star (fun a => W (g a) k)) =
      (W * star W).submatrix f g := by
  ext a b
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.star_apply]

/-- Establishes `sum_smul_vecMulVec_eq`: `∑ k, d k • vecMulVec (fun a => W (f a) k) (star (fun a => W (g a) k)) = (W * diagonal d * star W).submatrix f g`, for the stated parameters. -/
private theorem sum_smul_vecMulVec_eq {m n : Type*} [Fintype m] [DecidableEq m]
    (W : Matrix m m ℂ) (d : m → ℂ) (f g : n → m) :
    ∑ k, d k • vecMulVec (fun a => W (f a) k) (star (fun a => W (g a) k)) =
      (W * diagonal d * star W).submatrix f g := by
  ext a b
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.star_apply,
    Matrix.mul_diagonal, smul_eq_mul]
  ring

/-- Establishes `submatrix_fromBlocks₁₁`: `(Matrix.fromBlocks A B C D).submatrix Sum.inl Sum.inl = A`, for the stated parameters. -/
private theorem submatrix_fromBlocks₁₁ {n : Type*} (A B C D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).submatrix Sum.inl Sum.inl = A :=
  Matrix.ext fun _ _ => rfl

/-- Establishes `submatrix_fromBlocks₁₂`: `(Matrix.fromBlocks A B C D).submatrix Sum.inl Sum.inr = B`, for the stated parameters. -/
private theorem submatrix_fromBlocks₁₂ {n : Type*} (A B C D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).submatrix Sum.inl Sum.inr = B :=
  Matrix.ext fun _ _ => rfl

/-- Establishes `submatrix_fromBlocks₂₂`: `(Matrix.fromBlocks A B C D).submatrix Sum.inr Sum.inr = D`, for the stated parameters. -/
private theorem submatrix_fromBlocks₂₂ {n : Type*} (A B C D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).submatrix Sum.inr Sum.inr = D :=
  Matrix.ext fun _ _ => rfl

/-- Establishes `block_resolution_aux`: `∃ x y : n ⊕ n → n → ℂ, ∑ k, vecMulVec (x k) (star (x k)) = 1 ∧ ∑ k, vecMulVec (y k) (star (y k)) = 1 ∧ ∑ k, ((μ k : ℝ) : ℂ) • vecMulVec (x k) (star (y k)) = Bt ∧ ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (x k) (star (x k)) = Bt * Btᴴ ∧ ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (y k) (star (y k)) = Btᴴ * Bt`, for the stated parameters. -/
private theorem block_resolution_aux {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix (n ⊕ n) (n ⊕ n) ℂ) (μ : n ⊕ n → ℝ) (Bt : Matrix n n ℂ)
    (e1 : W * star W = Matrix.fromBlocks 1 0 0 1)
    (e2 : W * diagonal (fun k => ((μ k : ℝ) : ℂ)) * star W = Matrix.fromBlocks 0 Bt Btᴴ 0)
    (e3 : W * diagonal (fun k => ((μ k * μ k : ℝ) : ℂ)) * star W =
      Matrix.fromBlocks (Bt * Btᴴ) 0 0 (Btᴴ * Bt)) :
    ∃ x y : n ⊕ n → n → ℂ,
      ∑ k, vecMulVec (x k) (star (x k)) = 1 ∧
      ∑ k, vecMulVec (y k) (star (y k)) = 1 ∧
      ∑ k, ((μ k : ℝ) : ℂ) • vecMulVec (x k) (star (y k)) = Bt ∧
      ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (x k) (star (x k)) = Bt * Btᴴ ∧
      ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (y k) (star (y k)) = Btᴴ * Bt := by
  refine ⟨fun k a => W (Sum.inl a) k, fun k a => W (Sum.inr a) k, ?_, ?_, ?_, ?_, ?_⟩
  · have h := sum_vecMulVec_eq W (Sum.inl : n → n ⊕ n) Sum.inl
    rw [e1] at h
    exact h.trans (submatrix_fromBlocks₁₁ _ _ _ _)
  · have h := sum_vecMulVec_eq W (Sum.inr : n → n ⊕ n) Sum.inr
    rw [e1] at h
    exact h.trans (submatrix_fromBlocks₂₂ _ _ _ _)
  · have h := sum_smul_vecMulVec_eq W (fun k => ((μ k : ℝ) : ℂ)) (Sum.inl : n → n ⊕ n) Sum.inr
    rw [e2] at h
    exact h.trans (submatrix_fromBlocks₁₂ _ _ _ _)
  · have h := sum_smul_vecMulVec_eq W (fun k => ((μ k * μ k : ℝ) : ℂ))
      (Sum.inl : n → n ⊕ n) Sum.inl
    rw [e3] at h
    exact h.trans (submatrix_fromBlocks₁₁ _ _ _ _)
  · have h := sum_smul_vecMulVec_eq W (fun k => ((μ k * μ k : ℝ) : ℂ))
      (Sum.inr : n → n ⊕ n) Sum.inr
    rw [e3] at h
    exact h.trans (submatrix_fromBlocks₂₂ _ _ _ _)

/-- **Spectral resolution of the Hermitian dilation** `fromBlocks 0 Bt Btᴴ 0`, read off
blockwise: there are real numbers `μ k` and vectors `x k`, `y k` (the two halves of the
eigenvectors) resolving the identity twice, with `Bt = ∑ μ k • x k (y k)ᴴ`,
`Bt * Btᴴ = ∑ μ k ^ 2 • x k (x k)ᴴ` and `Btᴴ * Bt = ∑ μ k ^ 2 • y k (y k)ᴴ`. -/
theorem exists_block_resolution {n : Type*} [Fintype n] [DecidableEq n] (Bt : Matrix n n ℂ) :
    ∃ (μ : n ⊕ n → ℝ) (x y : n ⊕ n → n → ℂ),
      ∑ k, vecMulVec (x k) (star (x k)) = 1 ∧
      ∑ k, vecMulVec (y k) (star (y k)) = 1 ∧
      ∑ k, ((μ k : ℝ) : ℂ) • vecMulVec (x k) (star (y k)) = Bt ∧
      ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (x k) (star (x k)) = Bt * Btᴴ ∧
      ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (y k) (star (y k)) = Btᴴ * Bt := by
  have hd : (Matrix.fromBlocks (0 : Matrix n n ℂ) Bt Btᴴ 0).IsHermitian := by
    show (Matrix.fromBlocks (0 : Matrix n n ℂ) Bt Btᴴ 0)ᴴ = Matrix.fromBlocks 0 Bt Btᴴ 0
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_conjTranspose]
  have hWW : star (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
      (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 :=
    star_eigenvectorUnitary_mul_self hd
  have e1 : (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
      star (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) = Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.fromBlocks_one]
    exact mul_eq_one_comm.mp hWW
  have e2 : (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
      diagonal (fun k => ((hd.eigenvalues k : ℝ) : ℂ)) *
      star (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        Matrix.fromBlocks 0 Bt Btᴴ 0 :=
    (cfc_eq_mul hd (fun x => x)).symm.trans (cfc_id hd)
  have hsq : hd.cfc (fun x => x * x) = Matrix.fromBlocks (Bt * Btᴴ) 0 0 (Btᴴ * Bt) := by
    have h := cfc_mul_cfc hd (fun x => x) (fun x => x)
    rw [cfc_id hd, Matrix.fromBlocks_multiply] at h
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at h
    exact h.symm
  have e3 : (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
      diagonal (fun k => ((hd.eigenvalues k * hd.eigenvalues k : ℝ) : ℂ)) *
      star (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        Matrix.fromBlocks (Bt * Btᴴ) 0 0 (Btᴴ * Bt) :=
    (cfc_eq_mul hd (fun x => x * x)).symm.trans hsq
  exact ⟨hd.eigenvalues, block_resolution_aux
    (hd.eigenvectorUnitary : Matrix (n ⊕ n) (n ⊕ n) ℂ) hd.eigenvalues Bt e1 e2 e3⟩

/-! ### The decomposition -/

/-- The decomposition of `exists_ppt_decomposition`, indexed by `n ⊕ n`. -/
private theorem exists_ppt_decomposition_sum {n : Type*} [Fintype n] [DecidableEq n]
    {A B C : Matrix n n ℂ}
    (h₁ : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (h₂ : (Matrix.fromBlocks A Bᴴ B C).PosSemidef) :
    ∃ (lam : n ⊕ n → ℝ) (u v : n ⊕ n → n → ℂ) (R : Matrix n n ℂ),
      R.PosSemidef ∧
      C = ∑ k, (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k))) ∧
      B = ∑ k, ((2 * lam k : ℝ) : ℂ) • vecMulVec (u k) (star (v k)) ∧
      A = R + ∑ k, ((lam k ^ 2 : ℝ) : ℂ) •
        (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k))) := by
  obtain ⟨hC, hB1, hS1⟩ := posSemidef_fromBlocks_pinv h₁
  have h₂' : (Matrix.fromBlocks A Bᴴ Bᴴᴴ C).PosSemidef := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact h₂
  obtain ⟨-, hB2, hS2⟩ := posSemidef_fromBlocks_pinv h₂'
  rw [Matrix.conjTranspose_conjTranspose] at hS2
  have hCh : C.IsHermitian := hC.isHermitian
  have hPe : (C * pinv C)ᴴ = C * pinv C := (isHermitian_mul_pinv hCh).eq
  have hB3 : C * pinv C * B = B := by
    have h := congrArg Matrix.conjTranspose hB2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPe] at h
  have hB4 : C * pinv C * Bᴴ = Bᴴ := by
    have h := congrArg Matrix.conjTranspose hB1
    rwa [Matrix.conjTranspose_mul, hPe] at h
  obtain ⟨G, Gi, hGh, hGih, hGG, hGGi, hGiG, hGiGi⟩ := exists_half_sqrt hC
  obtain ⟨μ, x, y, hxx, hyy, hxy, hxx2, hyy2⟩ := exists_block_resolution (Gi * B * Gi)
  have hBt : (Gi * B * Gi)ᴴ = Gi * Bᴴ * Gi := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGih, Matrix.mul_assoc]
  -- the `C` identity
  have hCsum : ∑ k, (vecMulVec (G *ᵥ x k) (star (G *ᵥ x k)) +
      vecMulVec (G *ᵥ y k) (star (G *ᵥ y k))) = C := by
    rw [Finset.sum_add_distrib, sum_conj G hGh x x, sum_conj G hGh y y, hxx, hyy,
      Matrix.mul_one, hGG]
    exact half_add_half C
  -- the `B` identity
  have hin : ∑ k, ((2 * (μ k / 2) : ℝ) : ℂ) • vecMulVec (x k) (star (y k)) = Gi * B * Gi := by
    rw [← hxy]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (2 * (μ k / 2) : ℝ) = μ k by ring]
  have hBsum : ∑ k, ((2 * (μ k / 2) : ℝ) : ℂ) • vecMulVec (G *ᵥ x k) (star (G *ᵥ y k)) = B := by
    calc ∑ k, ((2 * (μ k / 2) : ℝ) : ℂ) • vecMulVec (G *ᵥ x k) (star (G *ᵥ y k))
        = G * (∑ k, ((2 * (μ k / 2) : ℝ) : ℂ) • vecMulVec (x k) (star (y k))) * G :=
          sum_smul_conj G hGh (fun k => ((2 * (μ k / 2) : ℝ) : ℂ)) x y
      _ = G * (Gi * B * Gi) * G := by rw [hin]
      _ = (G * Gi) * B * (Gi * G) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hGGi, hGiG, hB3, hB1]
  -- the `A` identity
  have hX : ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (G *ᵥ x k) (star (G *ᵥ x k)) =
      (2 : ℂ) • (B * pinv C * Bᴴ) := by
    calc ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (G *ᵥ x k) (star (G *ᵥ x k))
        = G * (∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (x k) (star (x k))) * G :=
          sum_smul_conj G hGh (fun k => ((μ k * μ k : ℝ) : ℂ)) x x
      _ = G * (Gi * B * Gi * (Gi * Bᴴ * Gi)) * G := by rw [hxx2, hBt]
      _ = (G * Gi) * B * (Gi * Gi) * Bᴴ * (Gi * G) := by simp only [Matrix.mul_assoc]
      _ = (2 : ℂ) • (B * pinv C * Bᴴ) := by
          rw [hGGi, hGiG, hGiGi, hB3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_assoc (B * pinv C) Bᴴ, hB2]
  have hY : ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (G *ᵥ y k) (star (G *ᵥ y k)) =
      (2 : ℂ) • (Bᴴ * pinv C * B) := by
    calc ∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (G *ᵥ y k) (star (G *ᵥ y k))
        = G * (∑ k, ((μ k * μ k : ℝ) : ℂ) • vecMulVec (y k) (star (y k))) * G :=
          sum_smul_conj G hGh (fun k => ((μ k * μ k : ℝ) : ℂ)) y y
      _ = G * (Gi * Bᴴ * Gi * (Gi * B * Gi)) * G := by rw [hyy2, hBt]
      _ = (G * Gi) * Bᴴ * (Gi * Gi) * B * (Gi * G) := by simp only [Matrix.mul_assoc]
      _ = (2 : ℂ) • (Bᴴ * pinv C * B) := by
          rw [hGGi, hGiG, hGiGi, hB4, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_assoc (Bᴴ * pinv C) B, hB1]
  have hc2 : ∀ k, (((μ k / 2) ^ 2 : ℝ) : ℂ) = (1 / 4 : ℂ) * ((μ k * μ k : ℝ) : ℂ) := by
    intro k
    push_cast
    ring
  have hAsum : ∑ k, (((μ k / 2) ^ 2 : ℝ) : ℂ) • (vecMulVec (G *ᵥ x k) (star (G *ᵥ x k)) +
      vecMulVec (G *ᵥ y k) (star (G *ᵥ y k))) =
      (1 / 4 : ℂ) • ((2 : ℂ) • (B * pinv C * Bᴴ) + (2 : ℂ) • (Bᴴ * pinv C * B)) := by
    calc ∑ k, (((μ k / 2) ^ 2 : ℝ) : ℂ) • (vecMulVec (G *ᵥ x k) (star (G *ᵥ x k)) +
          vecMulVec (G *ᵥ y k) (star (G *ᵥ y k)))
        = ∑ k, ((1 / 4 : ℂ) • (((μ k * μ k : ℝ) : ℂ) •
              vecMulVec (G *ᵥ x k) (star (G *ᵥ x k))) +
            (1 / 4 : ℂ) • (((μ k * μ k : ℝ) : ℂ) •
              vecMulVec (G *ᵥ y k) (star (G *ᵥ y k)))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hc2 k, mul_smul_add_split]
      _ = (1 / 4 : ℂ) • (∑ k, ((μ k * μ k : ℝ) : ℂ) •
              vecMulVec (G *ᵥ x k) (star (G *ᵥ x k))) +
            (1 / 4 : ℂ) • (∑ k, ((μ k * μ k : ℝ) : ℂ) •
              vecMulVec (G *ᵥ y k) (star (G *ᵥ y k))) := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = (1 / 4 : ℂ) • ((2 : ℂ) • (B * pinv C * Bᴴ) + (2 : ℂ) • (Bᴴ * pinv C * B)) := by
          rw [hX, hY, smul_add]
  have hR : (((1 / 2 : ℝ) : ℂ) • ((A - B * pinv C * Bᴴ) + (A - Bᴴ * pinv C * B))).PosSemidef :=
    posSemidef_half_smul (hS1.add hS2)
  refine ⟨fun k => μ k / 2, fun k => G *ᵥ x k, fun k => G *ᵥ y k,
    ((1 / 2 : ℝ) : ℂ) • ((A - B * pinv C * Bᴴ) + (A - Bᴴ * pinv C * B)), hR, hCsum.symm,
    hBsum.symm, ?_⟩
  exact (half_identity A (B * pinv C * Bᴴ) (Bᴴ * pinv C * B)).trans
    (congrArg (fun S => ((1 / 2 : ℝ) : ℂ) • ((A - B * pinv C * Bᴴ) + (A - Bᴴ * pinv C * B)) + S)
      hAsum.symm)

/-- **Simultaneous decomposition of a PPT pair.** If a block matrix `fromBlocks A B Bᴴ C` and its
partial transpose `fromBlocks A Bᴴ B C` are both positive semidefinite, then `C`, `B` and `A`
are simultaneously resolved by finitely many vectors `u k`, `v k` and real numbers `lam k`, up
to a positive semidefinite remainder `R` in the `A` corner. -/
theorem exists_ppt_decomposition {n : Type*} [Fintype n] [DecidableEq n] {A B C : Matrix n n ℂ}
    (h₁ : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (h₂ : (Matrix.fromBlocks A Bᴴ B C).PosSemidef) :
    ∃ (N : ℕ) (lam : Fin N → ℝ) (u v : Fin N → n → ℂ) (R : Matrix n n ℂ),
      R.PosSemidef ∧
      C = ∑ k, (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k))) ∧
      B = ∑ k, ((2 * lam k : ℝ) : ℂ) • vecMulVec (u k) (star (v k)) ∧
      A = R + ∑ k, ((lam k ^ 2 : ℝ) : ℂ) •
        (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k))) := by
  obtain ⟨s, u, v, R, _hs, hR, hC, hB, hA⟩ :=
    ManuscriptSVD.exists_ppt_decomposition_rank_svd h₁ h₂
  exact ⟨C.rank, s, u, v, R, hR, hC, hB, hA⟩

end Qatlib.Foundations.PPTMatrix.OperatorCones
