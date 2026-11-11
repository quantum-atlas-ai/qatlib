/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# GaussBosonic24.MainResults — phase-space model

Paper: *Gate-based quantum simulation of Gaussian bosonic circuits on
exponentially many modes*, fixed arXiv:2407.06290 (2024).

This module builds the finite-dimensional phase-space model that the paper uses
for the Supplemental Propositions.  A Gaussian-bosonic generator is a real
symmetric `2M × 2M` matrix `K` in the quadratic form `Ĥ = ½ ẑᵀ K ẑ`
(Eq. (A9)), with `ẑ = (q̂₁, …, q̂_M, p̂₁, …, p̂_M)` and the symplectic form

`Ω = iY ⊗ 1_M = [[0, 1_M], [-1_M, 0]]`   (Eq. (A7)).

The index type `Fin M ⊕ Fin M` is the paper's `2M`-dimensional phase space split
into the `M` position coordinates (`Sum.inl`) and the `M` momentum coordinates
(`Sum.inr`); it is definitionally the index type produced by `Matrix.fromBlocks`
so all block algebra is available.

The two gate-generator families that the paper feeds into the Supplemental
Propositions are represented directly,
* particle preserving, Eq. (A35)/(A37): `K(h) = [[Re h, -Im h], [Im h, Re h]]`
  with `h` Hermitian;
* non-particle preserving, Eq. (A38)/(A39): `K(Δ) = [[Re Δ, Im Δ], [Im Δ, -Re Δ]]`
  with `Δ` symmetric.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.GaussBosonic24.MomentPropagate

/-- Real part of a complex matrix, entrywise (used to write the real block
matrices of the paper's generators inside `ℂ`-matrices). -/
def rePart {I J : Type*} (A : Matrix I J ℂ) : Matrix I J ℂ := fun i j => (A i j).re

/-- Imaginary part of a complex matrix, entrywise. -/
def imPart {I J : Type*} (A : Matrix I J ℂ) : Matrix I J ℂ := fun i j => (A i j).im

/-- The `rePart_apply` result for the GaussBosonic24 paper model. -/
@[simp] theorem rePart_apply {I J : Type*} (A : Matrix I J ℂ) (i : I) (j : J) :
    rePart A i j = (A i j).re := rfl

/-- The `imPart_apply` result for the GaussBosonic24 paper model. -/
@[simp] theorem imPart_apply {I J : Type*} (A : Matrix I J ℂ) (i : I) (j : J) :
    imPart A i j = (A i j).im := rfl

/-- `star` fixes a real number, viewed as a complex number. -/
theorem star_ofReal_eq (r : ℝ) : star (r : ℂ) = (r : ℂ) :=
  Complex.conj_ofReal r

/-- The conjugate transpose of a real-part matrix is its transpose. -/
theorem rePart_conjTranspose {I J : Type*} (A : Matrix I J ℂ) :
    (rePart A)ᴴ = (rePart A)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, rePart_apply, star_ofReal_eq]

/-- The conjugate transpose of an imaginary-part matrix is its transpose. -/
theorem imPart_conjTranspose {I J : Type*} (A : Matrix I J ℂ) :
    (imPart A)ᴴ = (imPart A)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, imPart_apply, star_ofReal_eq]

/-- The symplectic form `Ω = iY ⊗ 1_M = [[0, 1], [-1, 0]]` of Eq. (A7) on the
phase-space split `Fin M ⊕ Fin M` (positions on the left, momenta on the right). -/
def omega (M : ℕ) : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ :=
  fromBlocks 0 1 (-1) 0

/-- `Ω` is real: its entries are real numbers. -/
theorem omega_rePart (M : ℕ) : rePart (omega M) = omega M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [omega, rePart, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply]
  all_goals
    first
      | (split_ifs <;> simp)
      | simp

/-- `Ω` is real and antisymmetric: `Ωᵀ = -Ω` (Eq. (A7)). -/
theorem omega_transpose (M : ℕ) : (omega M)ᵀ = -omega M := by
  rw [omega, fromBlocks_transpose, fromBlocks_neg]
  simp

/-- `Ω` is skew-Hermitian: `Ωᴴ = -Ω`.  Since `Ω` is real this is its
antisymmetry `omega_transpose`. -/
theorem omega_conjTranspose (M : ℕ) : (omega M)ᴴ = -omega M := by
  rw [← omega_rePart M, rePart_conjTranspose, omega_rePart M]
  exact omega_transpose M

/-- `Ω² = -1` on phase space (the complex structure of the symplectic form). -/
theorem omega_mul_self (M : ℕ) : omega M * omega M = -1 := by
  rw [omega, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

/-- The particle-preserving block matrix attached to a Hermitian coefficient
matrix `h`, Eq. (A37): `K = [[Re h, -Im h], [Im h, Re h]]`. -/
def particleK {M : ℕ} (h : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ :=
  fromBlocks (rePart h) (-(imPart h)) (imPart h) (rePart h)

/-- The non-particle-preserving block matrix attached to a symmetric
coefficient matrix `Δ`, Eq. (A39): `K = [[Re Δ, Im Δ], [Im Δ, -Re Δ]]`. -/
def nonParticleK {M : ℕ} (Δ : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ :=
  fromBlocks (rePart Δ) (imPart Δ) (imPart Δ) (-(rePart Δ))

/-! ## Elementary consequences of Hermiticity / symmetry -/

variable {M : ℕ}

/-- Taking `star` of a Hermitian-matrix entry relates the two off-diagonal entries. -/
theorem eq_star_of_isHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian)
    (i j : Fin M) : h j i = star (h i j) := by
  have hstar := congrFun (congrFun hh i) j
  simp only [Matrix.conjTranspose_apply] at hstar
  have := congrArg star hstar
  simpa using this

/-- The real part of a Hermitian matrix is symmetric. -/
theorem rePart_transpose_of_isHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian) :
    (rePart h)ᵀ = rePart h := by
  ext i j
  have hre : (h j i).re = (h i j).re := by
    rw [eq_star_of_isHermitian hh i j]
    rfl
  simp [rePart, hre]

/-- The real part of a Hermitian matrix is Hermitian. -/
theorem rePart_isHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian) :
    (rePart h).IsHermitian := by
  ext i j
  have hre : (h j i).re = (h i j).re := by
    rw [eq_star_of_isHermitian hh i j]
    rfl
  simp [rePart, hre, star_ofReal_eq]

/-- The imaginary part of a Hermitian matrix is antisymmetric. -/
theorem imPart_transpose_of_isHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian) :
    (imPart h)ᵀ = -imPart h := by
  ext i j
  have him : (h j i).im = -(h i j).im := by
    rw [eq_star_of_isHermitian hh i j]
    rfl
  simp [imPart, him]

/-- The imaginary part of a Hermitian matrix is skew-Hermitian. -/
theorem imPart_skewHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian) :
    (imPart h)ᴴ = -imPart h := by
  ext i j
  have him : (h j i).im = -(h i j).im := by
    rw [eq_star_of_isHermitian hh i j]
    rfl
  simp [imPart, him, star_ofReal_eq]

/-- The real part of a symmetric matrix is symmetric. -/
theorem rePart_transpose_of_transpose {Δ : Matrix (Fin M) (Fin M) ℂ}
    (hΔ : Δᵀ = Δ) : (rePart Δ)ᵀ = rePart Δ := by
  ext i j
  have h := congrFun (congrFun hΔ i) j
  simp only [Matrix.transpose_apply] at h
  simp [rePart, congrArg Complex.re h]

/-- The imaginary part of a symmetric matrix is symmetric. -/
theorem imPart_transpose_of_transpose {Δ : Matrix (Fin M) (Fin M) ℂ}
    (hΔ : Δᵀ = Δ) : (imPart Δ)ᵀ = imPart Δ := by
  ext i j
  have h := congrFun (congrFun hΔ i) j
  simp only [Matrix.transpose_apply] at h
  simp [imPart, congrArg Complex.im h]

end Qatlib.Papers.GaussBosonic24.MomentPropagate
