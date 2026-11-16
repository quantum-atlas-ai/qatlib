/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SupportedSVD

@[expose] public section




/-!
# The three identities for the prescribed supported-SVD components.

Expanding the supported singular vectors reconstructs the off-diagonal matrix, its two weighted Gram products, and the common diagonal corner. All singular slots are retained, so the formulas also cover rank-zero and zero-singular-value cases.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

omit [Fintype n] [DecidableEq n] in
/-- Establishes `sum_weighted_column_outer`: `(∑ j, d j • vecMulVec (Uᵀ j) (star (Vᵀ j))) = U * diagonal d * Vᴴ`, for the stated parameters. -/
theorem sum_weighted_column_outer (U V : Matrix n r ℂ) (d : r → ℂ) :
    (∑ j, d j • vecMulVec (Uᵀ j) (star (Vᵀ j))) = U * diagonal d * Vᴴ := by
  apply Matrix.ext
  intro a b
  have hentry : (U * diagonal d * Vᴴ) a b =
      ∑ j, (U a j * d j) * star (V b j) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [hentry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.transpose_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] [DecidableEq n] in
/-- Establishes `sum_column_outer`: `(∑ j, vecMulVec (Uᵀ j) (star (Uᵀ j))) = U * Uᴴ`, for the stated parameters. -/
theorem sum_column_outer (U : Matrix n r ℂ) :
    (∑ j, vecMulVec (Uᵀ j) (star (Uᵀ j))) = U * Uᴴ := by
  simpa only [one_smul, Matrix.diagonal_one, Matrix.mul_one] using
    sum_weighted_column_outer U U (fun _ => 1)

omit [DecidableEq n] in
/-- Squaring an SVD gives the spectral expansion of its left Gram matrix. -/
theorem svd_mul_conjTranspose (U V : Matrix n r ℂ) (s : r → ℝ)
    (hV : Vᴴ * V = 1) :
    (U * diagonal (fun j => (s j : ℂ)) * Vᴴ) *
      (U * diagonal (fun j => (s j : ℂ)) * Vᴴ)ᴴ =
    U * diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ)) * Uᴴ := by
  let D : Matrix r r ℂ := diagonal (fun j => (s j : ℂ))
  have hD : Dᴴ = D := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  have hD2 : D * D = diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ)) := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp only [pow_two, Complex.ofReal_mul]
  change (U * D * Vᴴ) * (U * D * Vᴴ)ᴴ = _
  calc
    (U * D * Vᴴ) * (U * D * Vᴴ)ᴴ = U * D * (Vᴴ * V) * D * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
        Matrix.mul_assoc]
    _ = U * (D * D) * Uᴴ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hD2]

/-- For the prescribed supported singular vectors, the three simultaneous
identities in Eq.(14) hold exactly, including zero singular values. -/
theorem supported_svd_component_identities
    (B C : Matrix n n ℂ) (U V : Matrix n r ℂ) (s : r → ℝ)
    (hC : C.PosSemidef) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hUU : U * Uᴴ = C * pinv C) (hVV : V * Vᴴ = C * pinv C)
    (hPB : C * pinv C * B = B) (hBP : B * (C * pinv C) = B)
    (hsvd : pinvSqrt C * B * pinvSqrt C =
      U * diagonal (fun j => (s j : ℂ)) * Vᴴ) :
    let p : r → n → ℂ := fun j => psqrt C *ᵥ Uᵀ j
    let q : r → n → ℂ := fun j => psqrt C *ᵥ Vᵀ j
    let D : r → Matrix n n ℂ := fun j => (1 / 2 : ℂ) •
      (vecMulVec (p j) (star (p j)) + vecMulVec (q j) (star (q j)))
    (∑ j, D j) = C ∧
      (∑ j, (s j : ℂ) • vecMulVec (p j) (star (q j))) = B ∧
      (∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j) =
        (1 / 2 : ℂ) • (B * pinv C * Bᴴ + Bᴴ * pinv C * B) := by
  let G := psqrt C
  let Gi := pinvSqrt C
  let P := C * pinv C
  let X := Gi * B * Gi
  have hG : Gᴴ = G := (isHermitian_psqrt hC).eq
  have hGi : Giᴴ = Gi := (isHermitian_pinvSqrt hC).eq
  have hP : Pᴴ = P := (isHermitian_mul_pinv hC.isHermitian).eq
  have hGG : G * G = C := psqrt_mul_psqrt hC
  have hGiGi : Gi * Gi = pinv C := pinvSqrt_mul_pinvSqrt hC
  have hGGi : G * Gi = P := psqrt_mul_pinvSqrt hC
  have hGiG : Gi * G = P := pinvSqrt_mul_psqrt hC
  have hPG : P * G = G := support_mul_psqrt C hC
  have hGP : G * P = G := by
    have h := congrArg Matrix.conjTranspose hPG
    simpa only [Matrix.conjTranspose_mul, hG, hP] using h
  have hPB' : P * Bᴴ = Bᴴ := by
    have h := congrArg Matrix.conjTranspose (show B * P = B from hBP)
    simpa only [Matrix.conjTranspose_mul, hP] using h
  have hBP' : Bᴴ * P = Bᴴ := by
    have h := congrArg Matrix.conjTranspose (show P * B = B from hPB)
    simpa only [Matrix.conjTranspose_mul, hP] using h
  have hX : Xᴴ = Gi * Bᴴ * Gi := by
    dsimp [X]
    simp only [Matrix.conjTranspose_mul, hGi, Matrix.mul_assoc]
  have hXback : G * X * G = B := by
    calc
      G * X * G = (G * Gi) * B * (Gi * G) := by dsimp [X]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hGGi, hGiG, hPB, hBP]
  have hXX : G * (X * Xᴴ) * G = B * pinv C * Bᴴ := by
    calc
      G * (X * Xᴴ) * G = (G * Gi) * B * (Gi * Gi) * Bᴴ * (Gi * G) := by
        rw [hX]; dsimp [X]; simp only [Matrix.mul_assoc]
      _ = B * pinv C * Bᴴ := by
        rw [hGGi, hGiG, hGiGi, hPB, Matrix.mul_assoc (B * pinv C), hBP']
  have hX'X : G * (Xᴴ * X) * G = Bᴴ * pinv C * B := by
    calc
      G * (Xᴴ * X) * G = (G * Gi) * Bᴴ * (Gi * Gi) * B * (Gi * G) := by
        rw [hX]; dsimp [X]; simp only [Matrix.mul_assoc]
      _ = Bᴴ * pinv C * B := by
        rw [hGGi, hGiG, hGiGi, hPB', Matrix.mul_assoc (Bᴴ * pinv C), hBP]
  have hUV : ∀ (M N : Matrix n r ℂ) (d : r → ℂ),
      (∑ j, d j • vecMulVec (G *ᵥ Mᵀ j) (star (G *ᵥ Nᵀ j))) =
        G * (M * diagonal d * Nᴴ) * G := by
    intro M N d
    rw [← sum_weighted_column_outer, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.star_mulVec, hG]
  have hsum (M : Matrix n r ℂ) (hMM : M * Mᴴ = P) :
      (∑ j, vecMulVec (G *ᵥ Mᵀ j) (star (G *ᵥ Mᵀ j))) = C := by
    have h := hUV M M (fun _ => 1)
    simpa only [one_smul, Matrix.diagonal_one, Matrix.mul_one, hMM, hGP, hGG] using h
  have hdiag : (diagonal (fun j => (s j : ℂ)) : Matrix r r ℂ)ᴴ =
      diagonal (fun j => (s j : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  have hrev : Xᴴ = V * diagonal (fun j => (s j : ℂ)) * Uᴴ := by
    change (pinvSqrt C * B * pinvSqrt C)ᴴ = _
    rw [hsvd, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hdiag]
    simp only [Matrix.mul_assoc]
  have hweightedU : (∑ j, ((s j ^ 2 : ℝ) : ℂ) •
      vecMulVec (G *ᵥ Uᵀ j) (star (G *ᵥ Uᵀ j))) = B * pinv C * Bᴴ := by
    rw [hUV, ← svd_mul_conjTranspose U V s hV, ← hsvd]
    exact hXX
  have hweightedV : (∑ j, ((s j ^ 2 : ℝ) : ℂ) •
      vecMulVec (G *ᵥ Vᵀ j) (star (G *ᵥ Vᵀ j))) = Bᴴ * pinv C * B := by
    rw [hUV, ← svd_mul_conjTranspose V U s hU, ← hrev,
      Matrix.conjTranspose_conjTranspose]
    exact hX'X
  dsimp only
  change (∑ j, (1 / 2 : ℂ) • (vecMulVec (G *ᵥ Uᵀ j) (star (G *ᵥ Uᵀ j)) +
      vecMulVec (G *ᵥ Vᵀ j) (star (G *ᵥ Vᵀ j)))) = C ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.smul_sum, Finset.sum_add_distrib, hsum U hUU, hsum V hVV]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  · rw [hUV, ← hsvd]
    exact hXback
  · have hscale (j : r) (M N : Matrix n n ℂ) :
        ((s j ^ 2 : ℝ) : ℂ) • ((1 / 2 : ℂ) • (M + N)) =
        (1 / 2 : ℂ) • (((s j ^ 2 : ℝ) : ℂ) • M + ((s j ^ 2 : ℝ) : ℂ) • N) := by
      rw [← smul_add, smul_comm]
    simp_rw [hscale]
    rw [← Finset.smul_sum, Finset.sum_add_distrib, hweightedU, hweightedV]

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
