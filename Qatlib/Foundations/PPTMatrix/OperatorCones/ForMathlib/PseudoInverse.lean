/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Module

@[expose] public section




/-!
# Pseudo-inverses and positive square roots of Hermitian matrices

This file develops, over `ℂ` and for finite index types:

* an explicit spectral calculus for a Hermitian matrix `C`, phrased through
  `Matrix.IsHermitian.cfc` (`cfc_mul_cfc`, `cfc_id`, `cfc_congr_eigenvalues`, `isHermitian_cfc`,
  `posSemidef_cfc`);
* the Moore–Penrose pseudo-inverse `pinv`, the positive square root `psqrt` and the
  pseudo-inverse square root `pinvSqrt`, together with the Penrose identities;
* the Gram form of the generalized Schur complement (`gram_mul_pinv_mul`,
  `posSemidef_gram_schur`) and Albert's block-positivity lemma (`posSemidef_fromBlocks_pinv`,
  `posSemidef_fromBlocks_pinv'`, `mulVec_eq_zero_of_posSemidef_fromBlocks`).
-/

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-! ### Scalar identities used on the eigenvalues -/

/-- Establishes `real_mul_inv_mul`: `x * x⁻¹ * x = x`, for the stated parameters. -/
private theorem real_mul_inv_mul (x : ℝ) : x * x⁻¹ * x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [mul_inv_cancel₀ hx, one_mul]

/-- Establishes `real_inv_mul_inv`: `x⁻¹ * x * x⁻¹ = x⁻¹`, for the stated parameters. -/
private theorem real_inv_mul_inv (x : ℝ) : x⁻¹ * x * x⁻¹ = x⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [inv_mul_cancel₀ hx, one_mul]

/-- Establishes `real_inv_sqrt_mul_inv_sqrt`: `(Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹`, for the stated parameters. -/
private theorem real_inv_sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hx]

/-- Establishes `real_sqrt_mul_inv_sqrt`: `Real.sqrt x * (Real.sqrt x)⁻¹ = x * x⁻¹`, for the stated parameters. -/
private theorem real_sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x * (Real.sqrt x)⁻¹ = x * x⁻¹ := by
  by_cases h0 : x = 0
  · simp [h0]
  · rw [mul_inv_cancel₀ ((Real.sqrt_ne_zero hx).mpr h0), mul_inv_cancel₀ h0]

/-- Establishes `real_inv_sqrt_mul_sqrt`: `(Real.sqrt x)⁻¹ * Real.sqrt x = x * x⁻¹`, for the stated parameters. -/
private theorem real_inv_sqrt_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * Real.sqrt x = x * x⁻¹ := by
  rw [mul_comm (Real.sqrt x)⁻¹ (Real.sqrt x), real_sqrt_mul_inv_sqrt hx]

open Matrix
open scoped ComplexOrder

/-! ### Explicit spectral calculus for a Hermitian matrix -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n ℂ}

/-- `Matrix.IsHermitian.cfc` unfolded as the triple product `U * diagonal (f ∘ eigenvalues) * U⋆`,
with `U` the eigenvector unitary. -/
theorem cfc_eq_mul (hC : C.IsHermitian) (f : ℝ → ℝ) :
    hC.cfc f = (hC.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) *
      star (hC.eigenvectorUnitary : Matrix n n ℂ) := by
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

/-- The eigenvector unitary `U` of a Hermitian matrix satisfies `U⋆ * U = 1`. -/
theorem star_eigenvectorUnitary_mul_self (hC : C.IsHermitian) :
    star (hC.eigenvectorUnitary : Matrix n n ℂ) * (hC.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
  exact Unitary.coe_star_mul_self hC.eigenvectorUnitary

/-- Conjugated diagonal matrices multiply entrywise when `U⋆ * U = 1`. -/
theorem conj_diagonal_mul_conj_diagonal {U : Matrix n n ℂ} (hU : star U * U = 1)
    (d e : n → ℂ) :
    (U * diagonal d * star U) * (U * diagonal e * star U) =
      U * diagonal (fun i => d i * e i) * star U := by
  calc (U * diagonal d * star U) * (U * diagonal e * star U)
      = U * diagonal d * (star U * U) * diagonal e * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal d * diagonal e) * star U := by
        rw [hU]
        simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = U * diagonal (fun i => d i * e i) * star U := by
        rw [Matrix.diagonal_mul_diagonal]

/-- The spectral calculus of a Hermitian matrix is multiplicative. -/
theorem cfc_mul_cfc (hC : C.IsHermitian) (f g : ℝ → ℝ) :
    hC.cfc f * hC.cfc g = hC.cfc (fun x => f x * g x) := by
  have hd : (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ) * ((g (hC.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((f (hC.eigenvalues i) * g (hC.eigenvalues i) : ℝ) : ℂ) :=
    funext fun i => (Complex.ofReal_mul _ _).symm
  rw [cfc_eq_mul hC f, cfc_eq_mul hC g, cfc_eq_mul hC (fun x => f x * g x)]
  refine Eq.trans (conj_diagonal_mul_conj_diagonal (star_eigenvectorUnitary_mul_self hC)
    (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) (fun i => ((g (hC.eigenvalues i) : ℝ) : ℂ))) ?_
  exact congrArg (fun d : n → ℂ => (hC.eigenvectorUnitary : Matrix n n ℂ) * diagonal d *
    star (hC.eigenvectorUnitary : Matrix n n ℂ)) hd

/-- The spectral calculus of the identity function returns the matrix itself. -/
theorem cfc_id (hC : C.IsHermitian) : hC.cfc (fun x => x) = C := by
  exact hC.spectral_theorem.symm

/-- The spectral calculus only depends on the values of the function on the eigenvalues. -/
theorem cfc_congr_eigenvalues (hC : C.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hC.eigenvalues i) = g (hC.eigenvalues i)) : hC.cfc f = hC.cfc g := by
  have hd : (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((g (hC.eigenvalues i) : ℝ) : ℂ) :=
    funext fun i => congrArg (fun x : ℝ => (x : ℂ)) (h i)
  rw [cfc_eq_mul hC f, cfc_eq_mul hC g]
  exact congrArg (fun d : n → ℂ => (hC.eigenvectorUnitary : Matrix n n ℂ) * diagonal d *
    star (hC.eigenvectorUnitary : Matrix n n ℂ)) hd

/-- The spectral calculus of a real function is Hermitian. -/
theorem isHermitian_cfc (hC : C.IsHermitian) (f : ℝ → ℝ) : (hC.cfc f).IsHermitian := by
  have hsa : star (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ) := by
    funext i
    exact Complex.conj_ofReal _
  have hd : (diagonal (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ hsa
  rw [cfc_eq_mul hC f]
  exact Matrix.isHermitian_mul_mul_conjTranspose _ hd

/-- The spectral calculus of a function that is nonnegative on the eigenvalues is positive
semidefinite. -/
theorem posSemidef_cfc (hC : C.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hC.eigenvalues i)) : (hC.cfc f).PosSemidef := by
  have hd : (diagonal (fun i => ((f (hC.eigenvalues i) : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.PosSemidef.diagonal (fun i => ?_)
    exact Complex.zero_le_real.mpr (hf i)
  rw [cfc_eq_mul hC f]
  exact hd.mul_mul_conjTranspose_same _

end Spectral

/-! ### Pseudo-inverse and square roots -/

section Pinv

variable {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n ℂ}

/-- Moore–Penrose pseudo-inverse of a Hermitian matrix: invert the nonzero eigenvalues, keep the
zero ones (`0⁻¹ = 0` in `ℝ`). Junk unless `C` is Hermitian. -/
noncomputable def pinv (C : Matrix n n ℂ) : Matrix n n ℂ := _root_.cfc (fun x : ℝ => x⁻¹) C

/-- Positive square root of a positive semidefinite matrix, via the functional calculus.
Junk unless `C` is Hermitian. -/
noncomputable def psqrt (C : Matrix n n ℂ) : Matrix n n ℂ :=
  _root_.cfc (fun x : ℝ => Real.sqrt x) C

/-- Square root of the pseudo-inverse of a positive semidefinite matrix. Junk unless `C` is
Hermitian. -/
noncomputable def pinvSqrt (C : Matrix n n ℂ) : Matrix n n ℂ :=
  _root_.cfc (fun x : ℝ => (Real.sqrt x)⁻¹) C

/-- Establishes `pinv_eq_cfc`: `pinv C = hC.cfc (fun x => x⁻¹)`, for the stated parameters. -/
theorem pinv_eq_cfc (hC : C.IsHermitian) : pinv C = hC.cfc (fun x => x⁻¹) := by
  exact hC.cfc_eq _

/-- Establishes `psqrt_eq_cfc`: `psqrt C = hC.cfc (fun x => Real.sqrt x)`, for the stated parameters. -/
theorem psqrt_eq_cfc (hC : C.IsHermitian) : psqrt C = hC.cfc (fun x => Real.sqrt x) := by
  exact hC.cfc_eq _

/-- Establishes `pinvSqrt_eq_cfc`: `pinvSqrt C = hC.cfc (fun x => (Real.sqrt x)⁻¹)`, for the stated parameters. -/
theorem pinvSqrt_eq_cfc (hC : C.IsHermitian) :
    pinvSqrt C = hC.cfc (fun x => (Real.sqrt x)⁻¹) := by
  exact hC.cfc_eq _

/-- Establishes `isHermitian_pinv`: `(pinv C).IsHermitian`, for the stated parameters. -/
theorem isHermitian_pinv (hC : C.IsHermitian) : (pinv C).IsHermitian := by
  rw [pinv_eq_cfc hC]
  exact isHermitian_cfc hC _

/-- `C * pinv C` is the spectral projection onto the range of `C`. -/
theorem mul_pinv_eq_cfc (hC : C.IsHermitian) : C * pinv C = hC.cfc (fun x => x * x⁻¹) := by
  calc C * pinv C
      = hC.cfc (fun x => x) * hC.cfc (fun x => x⁻¹) := by
        rw [cfc_id hC, ← pinv_eq_cfc hC]
    _ = hC.cfc (fun x => x * x⁻¹) := cfc_mul_cfc hC (fun x => x) (fun x => x⁻¹)

/-- Establishes `pinv_mul_eq_cfc`: `pinv C * C = hC.cfc (fun x => x⁻¹ * x)`, for the stated parameters. -/
theorem pinv_mul_eq_cfc (hC : C.IsHermitian) : pinv C * C = hC.cfc (fun x => x⁻¹ * x) := by
  calc pinv C * C
      = hC.cfc (fun x => x⁻¹) * hC.cfc (fun x => x) := by
        rw [cfc_id hC, ← pinv_eq_cfc hC]
    _ = hC.cfc (fun x => x⁻¹ * x) := cfc_mul_cfc hC (fun x => x⁻¹) (fun x => x)

/-- First Penrose identity. -/
theorem mul_pinv_mul (hC : C.IsHermitian) : C * pinv C * C = C := by
  calc C * pinv C * C
      = hC.cfc (fun x => x * x⁻¹) * hC.cfc (fun x => x) := by
        rw [← mul_pinv_eq_cfc hC, cfc_id hC]
    _ = hC.cfc (fun x => x * x⁻¹ * x) := cfc_mul_cfc hC (fun x => x * x⁻¹) (fun x => x)
    _ = hC.cfc (fun x => x) :=
        cfc_congr_eigenvalues hC (f := fun x => x * x⁻¹ * x) (g := fun x => x)
          (fun i => real_mul_inv_mul _)
    _ = C := cfc_id hC

/-- Second Penrose identity. -/
theorem pinv_mul_pinv (hC : C.IsHermitian) : pinv C * C * pinv C = pinv C := by
  calc pinv C * C * pinv C
      = hC.cfc (fun x => x⁻¹ * x) * hC.cfc (fun x => x⁻¹) := by
        rw [← pinv_mul_eq_cfc hC, ← pinv_eq_cfc hC]
    _ = hC.cfc (fun x => x⁻¹ * x * x⁻¹) := cfc_mul_cfc hC (fun x => x⁻¹ * x) (fun x => x⁻¹)
    _ = hC.cfc (fun x => x⁻¹) :=
        cfc_congr_eigenvalues hC (f := fun x => x⁻¹ * x * x⁻¹) (g := fun x => x⁻¹)
          (fun i => real_inv_mul_inv _)
    _ = pinv C := (pinv_eq_cfc hC).symm

/-- Establishes `mul_pinv_comm`: `C * pinv C = pinv C * C`, for the stated parameters. -/
theorem mul_pinv_comm (hC : C.IsHermitian) : C * pinv C = pinv C * C := by
  rw [mul_pinv_eq_cfc hC, pinv_mul_eq_cfc hC]
  exact cfc_congr_eigenvalues hC (f := fun x => x * x⁻¹) (g := fun x => x⁻¹ * x)
    (fun i => mul_comm _ _)

/-- Establishes `isHermitian_mul_pinv`: `(C * pinv C).IsHermitian`, for the stated parameters. -/
theorem isHermitian_mul_pinv (hC : C.IsHermitian) : (C * pinv C).IsHermitian := by
  rw [mul_pinv_eq_cfc hC]
  exact isHermitian_cfc hC _

/-- Establishes `posSemidef_pinv`: `(pinv C).PosSemidef`, for the stated parameters. -/
theorem posSemidef_pinv (hC : C.PosSemidef) : (pinv C).PosSemidef := by
  rw [pinv_eq_cfc hC.isHermitian]
  exact posSemidef_cfc hC.isHermitian (f := fun x => x⁻¹)
    (fun i => inv_nonneg.mpr (hC.eigenvalues_nonneg i))

/-- Establishes `posSemidef_psqrt`: `(psqrt C).PosSemidef`, for the stated parameters. -/
theorem posSemidef_psqrt (hC : C.PosSemidef) : (psqrt C).PosSemidef := by
  rw [psqrt_eq_cfc hC.isHermitian]
  exact posSemidef_cfc hC.isHermitian (f := fun x => Real.sqrt x)
    (fun i => Real.sqrt_nonneg _)

/-- Establishes `posSemidef_pinvSqrt`: `(pinvSqrt C).PosSemidef`, for the stated parameters. -/
theorem posSemidef_pinvSqrt (hC : C.PosSemidef) : (pinvSqrt C).PosSemidef := by
  rw [pinvSqrt_eq_cfc hC.isHermitian]
  exact posSemidef_cfc hC.isHermitian (f := fun x => (Real.sqrt x)⁻¹)
    (fun i => inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Establishes `isHermitian_psqrt`: `(psqrt C).IsHermitian`, for the stated parameters. -/
theorem isHermitian_psqrt (hC : C.PosSemidef) : (psqrt C).IsHermitian :=
  (posSemidef_psqrt hC).isHermitian

/-- Establishes `isHermitian_pinvSqrt`: `(pinvSqrt C).IsHermitian`, for the stated parameters. -/
theorem isHermitian_pinvSqrt (hC : C.PosSemidef) : (pinvSqrt C).IsHermitian :=
  (posSemidef_pinvSqrt hC).isHermitian

/-- Establishes `psqrt_mul_psqrt`: `psqrt C * psqrt C = C`, for the stated parameters. -/
theorem psqrt_mul_psqrt (hC : C.PosSemidef) : psqrt C * psqrt C = C := by
  have hH : C.IsHermitian := hC.isHermitian
  calc psqrt C * psqrt C
      = hH.cfc (fun x => Real.sqrt x) * hH.cfc (fun x => Real.sqrt x) := by
        rw [← psqrt_eq_cfc hH]
    _ = hH.cfc (fun x => Real.sqrt x * Real.sqrt x) :=
        cfc_mul_cfc hH (fun x => Real.sqrt x) (fun x => Real.sqrt x)
    _ = hH.cfc (fun x => x) :=
        cfc_congr_eigenvalues hH (f := fun x => Real.sqrt x * Real.sqrt x) (g := fun x => x)
          (fun i => Real.mul_self_sqrt (hC.eigenvalues_nonneg i))
    _ = C := cfc_id hH

/-- Establishes `pinvSqrt_mul_pinvSqrt`: `pinvSqrt C * pinvSqrt C = pinv C`, for the stated parameters. -/
theorem pinvSqrt_mul_pinvSqrt (hC : C.PosSemidef) : pinvSqrt C * pinvSqrt C = pinv C := by
  have hH : C.IsHermitian := hC.isHermitian
  calc pinvSqrt C * pinvSqrt C
      = hH.cfc (fun x => (Real.sqrt x)⁻¹) * hH.cfc (fun x => (Real.sqrt x)⁻¹) := by
        rw [← pinvSqrt_eq_cfc hH]
    _ = hH.cfc (fun x => (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹) :=
        cfc_mul_cfc hH (fun x => (Real.sqrt x)⁻¹) (fun x => (Real.sqrt x)⁻¹)
    _ = hH.cfc (fun x => x⁻¹) :=
        cfc_congr_eigenvalues hH (f := fun x => (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹)
          (g := fun x => x⁻¹)
          (fun i => real_inv_sqrt_mul_inv_sqrt (hC.eigenvalues_nonneg i))
    _ = pinv C := (pinv_eq_cfc hH).symm

/-- Establishes `psqrt_mul_pinvSqrt`: `psqrt C * pinvSqrt C = C * pinv C`, for the stated parameters. -/
theorem psqrt_mul_pinvSqrt (hC : C.PosSemidef) : psqrt C * pinvSqrt C = C * pinv C := by
  have hH : C.IsHermitian := hC.isHermitian
  calc psqrt C * pinvSqrt C
      = hH.cfc (fun x => Real.sqrt x) * hH.cfc (fun x => (Real.sqrt x)⁻¹) := by
        rw [← psqrt_eq_cfc hH, ← pinvSqrt_eq_cfc hH]
    _ = hH.cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) :=
        cfc_mul_cfc hH (fun x => Real.sqrt x) (fun x => (Real.sqrt x)⁻¹)
    _ = hH.cfc (fun x => x * x⁻¹) :=
        cfc_congr_eigenvalues hH (f := fun x => Real.sqrt x * (Real.sqrt x)⁻¹)
          (g := fun x => x * x⁻¹)
          (fun i => real_sqrt_mul_inv_sqrt (hC.eigenvalues_nonneg i))
    _ = C * pinv C := (mul_pinv_eq_cfc hH).symm

/-- Establishes `pinvSqrt_mul_psqrt`: `pinvSqrt C * psqrt C = C * pinv C`, for the stated parameters. -/
theorem pinvSqrt_mul_psqrt (hC : C.PosSemidef) : pinvSqrt C * psqrt C = C * pinv C := by
  have hH : C.IsHermitian := hC.isHermitian
  calc pinvSqrt C * psqrt C
      = hH.cfc (fun x => (Real.sqrt x)⁻¹) * hH.cfc (fun x => Real.sqrt x) := by
        rw [← psqrt_eq_cfc hH, ← pinvSqrt_eq_cfc hH]
    _ = hH.cfc (fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) :=
        cfc_mul_cfc hH (fun x => (Real.sqrt x)⁻¹) (fun x => Real.sqrt x)
    _ = hH.cfc (fun x => x * x⁻¹) :=
        cfc_congr_eigenvalues hH (f := fun x => (Real.sqrt x)⁻¹ * Real.sqrt x)
          (g := fun x => x * x⁻¹)
          (fun i => real_inv_sqrt_mul_sqrt (hC.eigenvalues_nonneg i))
    _ = C * pinv C := (mul_pinv_eq_cfc hH).symm

/-- A positive semidefinite matrix is the Gram matrix of its positive square root. -/
theorem conjTranspose_psqrt_mul_psqrt (hC : C.PosSemidef) : (psqrt C)ᴴ * psqrt C = C := by
  rw [(isHermitian_psqrt hC).eq, psqrt_mul_psqrt hC]

end Pinv

/-! ### Gram form of the generalized Schur complement and Albert's lemma -/

section Gram

/-- If `P` is a generalized inverse of the Gram matrix `Gᴴ * G`, then `G * (P * (Gᴴ * G)) = G`. -/
theorem gram_mul_ginv_mul {r n : Type*} [Fintype r] [Fintype n]
    (G : Matrix r n ℂ) (P : Matrix n n ℂ)
    (h1 : Gᴴ * G * P * (Gᴴ * G) = Gᴴ * G) : G * (P * (Gᴴ * G)) = G := by
  have hGZ : Gᴴ * (G - G * (P * (Gᴴ * G))) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc Gᴴ G, ← Matrix.mul_assoc (Gᴴ * G) P, h1, sub_self]
  have hZ : (G - G * (P * (Gᴴ * G)))ᴴ * (G - G * (P * (Gᴴ * G))) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul G, Matrix.sub_mul,
      Matrix.mul_assoc _ Gᴴ, hGZ, Matrix.mul_zero, sub_zero]
  have hZ0 : G - G * (P * (Gᴴ * G)) = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hZ
  exact (sub_eq_zero.mp hZ0).symm

/-- A matrix is fixed by right multiplication with the range projection of its Gram matrix. -/
theorem gram_mul_pinv_mul {r n : Type*} [Fintype r] [Fintype n] [DecidableEq n]
    (G : Matrix r n ℂ) : G * (pinv (Gᴴ * G) * (Gᴴ * G)) = G :=
  gram_mul_ginv_mul G (pinv (Gᴴ * G))
    (mul_pinv_mul (Matrix.isHermitian_conjTranspose_mul_self G))

/-- Gram form of the generalized Schur complement, for any Hermitian reflexive generalized
inverse `P` of `G₂ᴴ * G₂`. -/
theorem posSemidef_gram_sub_of_ginv {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]
    (G₁ : Matrix r m ℂ) (G₂ : Matrix r n ℂ) (P : Matrix n n ℂ) (hP : P.IsHermitian)
    (hPCP : P * (G₂ᴴ * G₂) * P = P) :
    (G₁ᴴ * G₁ - (G₁ᴴ * G₂) * P * (G₂ᴴ * G₁)).PosSemidef := by
  classical
  have hEh : (G₂ * P * G₂ᴴ)ᴴ = G₂ * P * G₂ᴴ :=
    (Matrix.isHermitian_mul_mul_conjTranspose G₂ hP).eq
  have hEE : (G₂ * P * G₂ᴴ) * (G₂ * P * G₂ᴴ) = G₂ * P * G₂ᴴ := by
    calc (G₂ * P * G₂ᴴ) * (G₂ * P * G₂ᴴ)
        = G₂ * (P * (G₂ᴴ * G₂) * P) * G₂ᴴ := by simp only [Matrix.mul_assoc]
      _ = G₂ * P * G₂ᴴ := by rw [hPCP]
  have h1E : (1 - G₂ * P * G₂ᴴ)ᴴ * (1 - G₂ * P * G₂ᴴ) = 1 - G₂ * P * G₂ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hEh, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, hEE, sub_self, sub_zero]
  have hpsd : (1 - G₂ * P * G₂ᴴ).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - G₂ * P * G₂ᴴ)
    rw [h1E] at h
    exact h
  have hexpr : G₁ᴴ * G₁ - (G₁ᴴ * G₂) * P * (G₂ᴴ * G₁) = G₁ᴴ * (1 - G₂ * P * G₂ᴴ) * G₁ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hexpr]
  exact hpsd.conjTranspose_mul_mul_same G₁

/-- Gram form of the generalized Schur complement: the Gram matrix of `G₁`, minus its component
along the range of `G₂`, is positive semidefinite. -/
theorem posSemidef_gram_schur {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]
    [DecidableEq n] (G₁ : Matrix r m ℂ) (G₂ : Matrix r n ℂ) :
    (G₁ᴴ * G₁ - (G₁ᴴ * G₂) * pinv (G₂ᴴ * G₂) * (G₂ᴴ * G₁)).PosSemidef :=
  posSemidef_gram_sub_of_ginv G₁ G₂ (pinv (G₂ᴴ * G₂))
    (isHermitian_pinv (Matrix.isHermitian_conjTranspose_mul_self G₂))
    (pinv_mul_pinv (Matrix.isHermitian_conjTranspose_mul_self G₂))

/-- Albert's block-positivity lemma (both versions) for a block matrix given with a Gram
factorization `Gᴴ * G`. -/
theorem posSemidef_fromBlocks_of_gram {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] [Fintype r] {A : Matrix m m ℂ} {B : Matrix m n ℂ} {C : Matrix n n ℂ}
    (G : Matrix r (m ⊕ n) ℂ) (hG : Gᴴ * G = Matrix.fromBlocks A B Bᴴ C) :
    (C.PosSemidef ∧ B * (C * pinv C) = B ∧ (A - B * pinv C * Bᴴ).PosSemidef) ∧
      (A.PosSemidef ∧ A * pinv A * B = B ∧ (C - Bᴴ * pinv A * B).PosSemidef) := by
  have hA : (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inl = A := by
    ext i j
    exact congrFun (congrFun hG (Sum.inl i)) (Sum.inl j)
  have hB : (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr = B := by
    ext i j
    exact congrFun (congrFun hG (Sum.inl i)) (Sum.inr j)
  have hB' : (G.submatrix id Sum.inr)ᴴ * G.submatrix id Sum.inl = Bᴴ := by
    ext i j
    exact congrFun (congrFun hG (Sum.inr i)) (Sum.inl j)
  have hC : (G.submatrix id Sum.inr)ᴴ * G.submatrix id Sum.inr = C := by
    ext i j
    exact congrFun (congrFun hG (Sum.inr i)) (Sum.inr j)
  have hCpsd : C.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (G.submatrix id Sum.inr)
    rw [hC] at h
    exact h
  have hApsd : A.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (G.submatrix id Sum.inl)
    rw [hA] at h
    exact h
  have hCh : C.IsHermitian := hCpsd.isHermitian
  have hAh : A.IsHermitian := hApsd.isHermitian
  have hg2 : G.submatrix id Sum.inr * (pinv C * C) = G.submatrix id Sum.inr := by
    have h := gram_mul_pinv_mul (G.submatrix id Sum.inr)
    rw [hC] at h
    exact h
  have hg1 : G.submatrix id Sum.inl * (pinv A * A) = G.submatrix id Sum.inl := by
    have h := gram_mul_pinv_mul (G.submatrix id Sum.inl)
    rw [hA] at h
    exact h
  have hg1' : A * pinv A * (G.submatrix id Sum.inl)ᴴ = (G.submatrix id Sum.inl)ᴴ := by
    have h := congrArg Matrix.conjTranspose hg1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAh.eq,
      (isHermitian_pinv hAh).eq] at h
    exact h
  have h2 : B * (C * pinv C) = B := by
    calc B * (C * pinv C) = B * (pinv C * C) := by rw [mul_pinv_comm hCh]
      _ = (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr * (pinv C * C) := by rw [hB]
      _ = (G.submatrix id Sum.inl)ᴴ * (G.submatrix id Sum.inr * (pinv C * C)) := by
          rw [Matrix.mul_assoc]
      _ = (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr := by rw [hg2]
      _ = B := hB
  have h3 : (A - B * pinv C * Bᴴ).PosSemidef := by
    have h := posSemidef_gram_schur (G.submatrix id Sum.inl) (G.submatrix id Sum.inr)
    rw [hA, hB, hC, hB'] at h
    exact h
  have h2' : A * pinv A * B = B := by
    calc A * pinv A * B
        = A * pinv A * ((G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr) := by rw [hB]
      _ = A * pinv A * (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr := by
          simp only [Matrix.mul_assoc]
      _ = (G.submatrix id Sum.inl)ᴴ * G.submatrix id Sum.inr := by rw [hg1']
      _ = B := hB
  have h3' : (C - Bᴴ * pinv A * B).PosSemidef := by
    have h := posSemidef_gram_schur (G.submatrix id Sum.inr) (G.submatrix id Sum.inl)
    rw [hC, hB', hA, hB] at h
    exact h
  exact ⟨⟨hCpsd, h2, h3⟩, ⟨hApsd, h2', h3'⟩⟩

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : Matrix m m ℂ} {B : Matrix m n ℂ} {C : Matrix n n ℂ}

/-- **Albert's lemma**: a positive semidefinite block matrix has a positive semidefinite corner
`C`, its off-diagonal block is supported on the range of `C`, and the generalized Schur
complement of `C` is positive semidefinite. -/
theorem posSemidef_fromBlocks_pinv (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    C.PosSemidef ∧ B * (C * pinv C) = B ∧ (A - B * pinv C * Bᴴ).PosSemidef :=
  (posSemidef_fromBlocks_of_gram (psqrt (Matrix.fromBlocks A B Bᴴ C))
    (conjTranspose_psqrt_mul_psqrt h)).1

/-- **Albert's lemma**, mirrored: the same statement with the roles of the two diagonal blocks
exchanged. -/
theorem posSemidef_fromBlocks_pinv' (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    A.PosSemidef ∧ (A * pinv A) * B = B ∧ (C - Bᴴ * pinv A * B).PosSemidef :=
  (posSemidef_fromBlocks_of_gram (psqrt (Matrix.fromBlocks A B Bᴴ C))
    (conjTranspose_psqrt_mul_psqrt h)).2

/-- In a positive semidefinite block matrix, the kernel of the corner `C` is contained in the
kernel of the off-diagonal block `B`. -/
theorem mulVec_eq_zero_of_posSemidef_fromBlocks (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    ∀ z : n → ℂ, C *ᵥ z = 0 → B *ᵥ z = 0 := by
  intro z hz
  obtain ⟨hC, hB, -⟩ := posSemidef_fromBlocks_pinv h
  have hB' : B * (pinv C * C) = B := by
    rw [← mul_pinv_comm hC.isHermitian]
    exact hB
  calc B *ᵥ z = (B * (pinv C * C)) *ᵥ z := by rw [hB']
    _ = B *ᵥ (pinv C *ᵥ (C *ᵥ z)) := by simp only [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hz, Matrix.mulVec_zero, Matrix.mulVec_zero]

end Gram

end Qatlib.Foundations.PPTMatrix.OperatorCones
