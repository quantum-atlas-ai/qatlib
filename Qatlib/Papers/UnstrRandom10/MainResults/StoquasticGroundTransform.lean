/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Complex.BigOperators

set_option backward.isDefEq.respectTransparency false

/-!
# UnstrRandom10.MainResults: the stoquastic ground-state transform

Farhi--Goldstone--Gosset--Shor, *Unstructured Randomness, Small Gaps and
Localization*, fixed arXiv:1010.0009v1.

Section II.1 of the paper (extracted-text lines 128--200, containing Theorem 4 and
Lemma 1) obtains variational *lower* bounds on the ground state energy of a
stoquastic Hamiltonian from the Collatz--Wielandt min-max principle. The proof
rests on one structural fact: a real symmetric matrix that is stoquastic in the
computational basis and annihilates a pointwise positive vector is positive
semidefinite (the ground-state transform).

This module develops that fact together with the quadratic-form bookkeeping that
the paper-level statements use. Stoquasticity is basis dependent, and the paper
states its results for Hermitian operators whose `|z⟩`-basis matrix elements are
real. The real symmetric matrix used here is the standard real representative of
such an operator.

Boundary: nothing here models the random-permutation Hamiltonian `H_π(s)`, the
adiabatic theorem, or any asymptotic probability statement.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.UnstrRandom10.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real matrix is *stoquastic* in the standard basis when it is symmetric and all
off-diagonal entries are nonpositive, i.e. `⟨z|H|z'⟩ ≤ 0` for `z ≠ z'` as in
arXiv:1010.0009v1, Section II.1. -/
def IsStoquastic (H : Matrix ι ι ℝ) : Prop :=
  (∀ i j, H j i = H i j) ∧ ∀ i j, i ≠ j → H i j ≤ 0

/-- The quadratic form `⟨u|H|u⟩` of a real matrix at a real amplitude vector. -/
def qform (H : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (H *ᵥ u)

/-- The real-part matrix of a complex matrix. The paper's stoquastic operators have
real `|z⟩`-basis matrix elements, so their real part is the matrix entry itself. -/
def reMatrix (H : Matrix ι ι ℂ) : Matrix ι ι ℝ := fun i j => (H i j).re

omit [Fintype ι] [DecidableEq ι] in
/-- Representation bridge: a Hermitian complex matrix whose off-diagonal entries have
nonpositive real parts is represented by a real stoquastic matrix. Since the paper's
stoquastic operators have real matrix elements, `(H i j).re` is the entry `⟨i|H|j⟩`
itself. -/
theorem isStoquastic_reMatrix {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hoff : ∀ i j, i ≠ j → (H i j).re ≤ 0) : IsStoquastic (reMatrix H) := by
  refine ⟨fun i j => ?_, fun i j hij => hoff i j hij⟩
  have h : star (H j i) = H i j := (Matrix.IsHermitian.ext_iff.mp hH) i j
  have := congrArg Complex.re h
  simpa [reMatrix] using this

omit [DecidableEq ι] in
/-- Representation bridge for the quotients of Theorem 4: the real-part matrix acts on
real amplitudes by taking the real part of the complex matrix action, so the quotients
`⟨z|H|φ⟩ / ⟨z|φ⟩` computed in the real representation coincide with the real parts of
the complex ones. -/
lemma reMatrix_mulVec_apply {H : Matrix ι ι ℂ} (φ : ι → ℝ) (z : ι) :
    (reMatrix H *ᵥ φ) z = ((H *ᵥ fun z => (φ z : ℂ)) z).re := by
  simp only [reMatrix, Matrix.mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

omit [DecidableEq ι] in
/-- Laplacian form of the quadratic form of a matrix with vanishing row sums: for
such a symmetric `A` the quadratic form at `w` equals half the sum of the squared
differences over pairs. -/
lemma sum_half_identity (A : ι → ι → ℝ) (hAsym : ∀ i j, A j i = A i j)
    (hrow : ∀ i, ∑ j, A i j = 0) (w : ι → ℝ) :
    ∑ i, ∑ j, A i j * (w i * w j) = (1 / 2) * ∑ i, ∑ j, (-A i j) * (w i - w j) ^ 2 := by
  have hcol : ∀ j, ∑ i, A i j = 0 := by
    intro j
    rw [← hrow j]
    exact Finset.sum_congr rfl fun i _ => (hAsym i j).symm
  have h1 : ∑ i, ∑ j, A i j * w i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_mul]
    simp [hrow i]
  have h2 : ∑ i, ∑ j, A i j * w j ^ 2 = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_mul]
    simp [hcol j]
  have hexp : ∑ i, ∑ j, A i j * (w i - w j) ^ 2
      = -2 * ∑ i, ∑ j, A i j * (w i * w j) := by
    have hterm : ∀ i j, A i j * (w i - w j) ^ 2
        = A i j * w i ^ 2 - A i j * (w i * w j) - A i j * (w i * w j)
          + A i j * w j ^ 2 := by
      intro i j
      ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [h1, h2]
    ring
  have hneg : ∑ i, ∑ j, (-A i j) * (w i - w j) ^ 2
      = -∑ i, ∑ j, A i j * (w i - w j) ^ 2 := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hneg, hexp]
  ring

omit [DecidableEq ι] in
/-- Ground-state transform: a symmetric matrix whose off-diagonal entries are
nonpositive and which annihilates a pointwise positive vector is positive
semidefinite. This is the structural input to Lemma 1 of arXiv:1010.0009v1
(extracted-text line 142). -/
theorem posSemidef_of_stoquastic_kernel (K : Matrix ι ι ℝ) (hK : IsStoquastic K)
    (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) (hKψ : K *ᵥ ψ = 0) : K.PosSemidef := by
  obtain ⟨hKsym, hKoff⟩ := hK
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.IsHermitian.ext fun i j => ?_, fun u => ?_⟩
  · simpa using hKsym i j
  · set w : ι → ℝ := fun i => u i / ψ i
    have hu : ∀ i, ψ i * w i = u i := fun i => by
      simp only [w]
      exact mul_div_cancel₀ (u i) (ne_of_gt (hψ i))
    have hrow : ∀ i, ∑ j, (K i j * ψ i * ψ j) = 0 := by
      intro i
      have hi : ∑ j, K i j * ψ j = 0 := by
        simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using congr_fun hKψ i
      calc ∑ j, (K i j * ψ i * ψ j) = ψ i * ∑ j, K i j * ψ j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    have hAsym : ∀ i j, (K j i * ψ j * ψ i) = (K i j * ψ i * ψ j) := by
      intro i j
      rw [hKsym i j]
      ring
    have hq : u ⬝ᵥ (K *ᵥ u) = ∑ i, ∑ j, (K i j * ψ i * ψ j) * (w i * w j) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hu i, ← hu j]
      ring
    rw [show star u = u from star_trivial u, hq, sum_half_identity _ hAsym hrow w]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst hij
      simp
    · have h1 : 0 ≤ -(K i j * ψ i * ψ j) := by
        have hKij : K i j ≤ 0 := hKoff i j hij
        have hpr : 0 < ψ i * ψ j := mul_pos (hψ i) (hψ j)
        nlinarith
      exact mul_nonneg h1 (sq_nonneg _)

omit [DecidableEq ι] in
/-- `E` is the lowest eigenvalue of `H`: `E` is an eigenvalue and no eigenvalue of
`H` is smaller. -/
def IsLowestEigenvalue (H : Matrix ι ι ℝ) (E : ℝ) : Prop :=
  (∃ v, v ≠ 0 ∧ H *ᵥ v = E • v) ∧
    ∀ (μ : ℝ) (v : ι → ℝ), v ≠ 0 → H *ᵥ v = μ • v → E ≤ μ

/-- Quadratic form of a shift by a multiple of the identity:
`⟨u|(H - E·1)|u⟩ = ⟨u|H|u⟩ - E ⟨u|u⟩`. -/
lemma qform_sub_smul_one (H : Matrix ι ι ℝ) (E : ℝ) (u : ι → ℝ) :
    qform (H - E • (1 : Matrix ι ι ℝ)) u = qform H u - E * (u ⬝ᵥ u) := by
  rw [qform, qform, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

/-- Quadratic form of a shift by a diagonal matrix:
`⟨u|(H - diag d)|u⟩ = ⟨u|H|u⟩ - ∑ z, u z * d z * u z`. -/
lemma qform_sub_diagonal (H : Matrix ι ι ℝ) (d : ι → ℝ) (u : ι → ℝ) :
    qform (H - diagonal d) u = qform H u - ∑ i, u i * (d i * u i) := by
  rw [qform, qform, sub_mulVec, dotProduct_sub]
  congr 1
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [mulVec_diagonal]

omit [DecidableEq ι] in
/-- Quadratic form of an eigenvector: if `H v = μ v` then `⟨v|H|v⟩ = μ ⟨v|v⟩`. -/
lemma qform_of_eigenvector (H : Matrix ι ι ℝ) (v : ι → ℝ) (mu : ℝ) (hv : H *ᵥ v = mu • v) :
    qform H v = mu * (v ⬝ᵥ v) := by
  rw [qform, hv, dotProduct_smul, smul_eq_mul]

end Qatlib.Papers.UnstrRandom10.MainResults
