/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SchmidtBridges
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SingularValueDecomposition

@[expose] public section




/-!
# Singular value decomposition on the exact range of a positive matrix.

The support of a positive semidefinite corner is represented by an actual rectangular isometry. Compressing the off-diagonal block to this support, applying its singular decomposition, and lifting back reconstructs the original block and the pseudoinverse Gram expressions.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

omit [DecidableEq r] in
/-- An orthonormal basis of the actual range of a Hermitian matrix resolves
its Moore--Penrose support projector. -/
theorem isometry_range_projector (C : Matrix n n ℂ) (J : Matrix n r ℂ)
    (hC : C.IsHermitian) (hCJ : C = J * (Jᴴ * C))
    (hcol : ∀ j, ∃ z : n → ℂ, C *ᵥ z = Jᵀ j) :
    J * Jᴴ = C * pinv C := by
  let P := C * pinv C
  have hPC : P * C = C := mul_pinv_mul hC
  have hPh : Pᴴ = P := (isHermitian_mul_pinv hC).eq
  have hPJ : P * J = J := by
    ext i j
    obtain ⟨z, hz⟩ := hcol j
    have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ z) hPC
    rw [← Matrix.mulVec_mulVec, hz] at h
    exact congrFun h i
  have hJP : Jᴴ * P = Jᴴ := by
    have h := congrArg Matrix.conjTranspose hPJ
    simpa only [Matrix.conjTranspose_mul, hPh] using h
  calc
    J * Jᴴ = J * (Jᴴ * P) := by rw [hJP]
    _ = (J * (Jᴴ * C)) * pinv C := by dsimp [P]; simp only [Matrix.mul_assoc]
    _ = C * pinv C := by rw [← hCJ]

/-- Rank(C) columns, a literal orthonormal basis of Ran(C), with its complete
projector resolution; zero rank is included. -/
theorem exists_support_isometry (C : Matrix n n ℂ) (hC : C.IsHermitian) :
    ∃ J : Matrix n (Fin C.rank) ℂ,
      Jᴴ * J = 1 ∧ J * Jᴴ = C * pinv C ∧
        ∀ j, ∃ z : n → ℂ, C *ᵥ z = Jᵀ j := by
  obtain ⟨J, hJ, hCJ, hcol⟩ := ManuscriptSchmidt.exists_isometry_rank_factorization C
  exact ⟨J, hJ, isometry_range_projector C J hC hCJ hcol, hcol⟩

/-- The support projector fixes the positive square root on the left. -/
theorem support_mul_psqrt (C : Matrix n n ℂ) (hC : C.PosSemidef) :
    C * pinv C * psqrt C = psqrt C := by
  rw [mul_pinv_eq_cfc hC.isHermitian, psqrt_eq_cfc hC.isHermitian,
    cfc_mul_cfc]
  apply cfc_congr_eigenvalues
  intro i
  by_cases hi : hC.isHermitian.eigenvalues i = 0
  · simp [hi]
  · rw [mul_inv_cancel₀ hi, one_mul]

/-- The support projector also fixes the inverse square root. -/
theorem support_mul_pinvSqrt (C : Matrix n n ℂ) (hC : C.PosSemidef) :
    C * pinv C * pinvSqrt C = pinvSqrt C := by
  rw [mul_pinv_eq_cfc hC.isHermitian, pinvSqrt_eq_cfc hC.isHermitian,
    cfc_mul_cfc]
  apply cfc_congr_eigenvalues
  intro i
  by_cases hi : hC.isHermitian.eigenvalues i = 0
  · simp [hi]
  · rw [mul_inv_cancel₀ hi, one_mul]

omit [DecidableEq n] [DecidableEq r] in
/-- A supported operator equals its compression to any complete orthonormal
support basis followed by the inclusion back into the ambient space. -/
theorem reconstruct_support_compression (X P : Matrix n n ℂ) (J : Matrix n r ℂ)
    (hJ : J * Jᴴ = P) (hPX : P * X = X) (hXP : X * P = X) :
    X = J * (Jᴴ * X * J) * Jᴴ := by
  calc
    X = P * X * P := by rw [hPX, hXP]
    _ = J * (Jᴴ * X * J) * Jᴴ := by rw [← hJ]; simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Transport a square SVD on the support to two complete orthonormal
families in the ambient space. This lemma is pure algebra, with the genuine
compressed SVD supplied by the separate existence theorem. -/
theorem lift_compressed_svd
    (X P : Matrix n n ℂ) (J : Matrix n r ℂ)
    (U V : Matrix r r ℂ) (s : r → ℝ)
    (hJ : Jᴴ * J = 1) (hJJ : J * Jᴴ = P)
    (hPX : P * X = X) (hXP : X * P = X)
    (hU : U ∈ unitary (Matrix r r ℂ)) (hV : V ∈ unitary (Matrix r r ℂ))
    (hsvd : Jᴴ * X * J = U * diagonal (fun j => (s j : ℂ)) * Vᴴ) :
    (J * U)ᴴ * (J * U) = 1 ∧ (J * V)ᴴ * (J * V) = 1 ∧
      (J * U) * (J * U)ᴴ = P ∧ (J * V) * (J * V)ᴴ = P ∧
      X = (J * U) * diagonal (fun j => (s j : ℂ)) * (J * V)ᴴ := by
  have hU1 : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hU2 : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have hV1 : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hV2 : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc
      Uᴴ * Jᴴ * (J * U) = Uᴴ * (Jᴴ * J) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, hU1]
  · rw [Matrix.conjTranspose_mul]
    calc
      Vᴴ * Jᴴ * (J * V) = Vᴴ * (Jᴴ * J) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, hV1]
  · rw [Matrix.conjTranspose_mul]
    calc
      J * U * (Uᴴ * Jᴴ) = J * (U * Uᴴ) * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hU2, Matrix.mul_one, hJJ]
  · rw [Matrix.conjTranspose_mul]
    calc
      J * V * (Vᴴ * Jᴴ) = J * (V * Vᴴ) * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hV2, Matrix.mul_one, hJJ]
  · rw [reconstruct_support_compression X P J hJJ hPX hXP, hsvd,
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- Literal supported SVD: there are rank(C) slots, including zero singular
values, and both singular families resolve the entire support of C. The
whitened operator is supported even before assuming B itself is supported. -/
theorem exists_supported_svd (B C : Matrix n n ℂ) (hC : C.PosSemidef) :
    ∃ (U V : Matrix n (Fin C.rank) ℂ) (s : Fin C.rank → ℝ),
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      U * Uᴴ = C * pinv C ∧ V * Vᴴ = C * pinv C ∧
      (∀ j, 0 ≤ s j) ∧ pinvSqrt C * B * pinvSqrt C =
        U * diagonal (fun j => (s j : ℂ)) * Vᴴ := by
  classical
  obtain ⟨J, hJ, hJJ, -⟩ := exists_support_isometry C hC.isHermitian
  let X := pinvSqrt C * B * pinvSqrt C
  let P := C * pinv C
  have hPG : P * pinvSqrt C = pinvSqrt C := support_mul_pinvSqrt C hC
  have hGP : pinvSqrt C * P = pinvSqrt C := by
    have hPh : Pᴴ = P := (isHermitian_mul_pinv hC.isHermitian).eq
    have h := congrArg Matrix.conjTranspose hPG
    simpa only [Matrix.conjTranspose_mul, (isHermitian_pinvSqrt hC).eq, hPh] using h
  have hPX : P * X = X := by
    dsimp only [X]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPG]
  have hXP : X * P = X := by
    dsimp only [X]
    rw [Matrix.mul_assoc (pinvSqrt C * B), hGP]
  obtain ⟨U, V, s, hU, hV, hs, hsvd⟩ := exists_square_svd (Jᴴ * X * J)
  obtain ⟨hJU, hJV, hJUU, hJVV, hX⟩ :=
    lift_compressed_svd X P J U V s hJ hJJ hPX hXP hU hV hsvd
  exact ⟨J * U, J * V, s, hJU, hJV, hJUU, hJVV, hs, hX⟩

/-- The projector resolution and orthonormality imply literal range
membership of each basis vector, not merely an abstract support label. -/
theorem column_mem_range_of_support_resolution
    (C : Matrix n n ℂ) (U : Matrix n r ℂ)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = C * pinv C) (j : r) :
    ∃ z : n → ℂ, C *ᵥ z = Uᵀ j := by
  have hPU : (C * pinv C) * U = U := by
    rw [← hUU, Matrix.mul_assoc, hU, Matrix.mul_one]
  refine ⟨pinv C *ᵥ Uᵀ j, ?_⟩
  rw [Matrix.mulVec_mulVec]
  funext i
  exact congrFun (congrFun hPU i) j

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
