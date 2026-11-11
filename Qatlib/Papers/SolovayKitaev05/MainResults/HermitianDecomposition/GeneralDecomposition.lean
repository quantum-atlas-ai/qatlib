/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Hermitian commutator decompositions in finite dimension

This module develops an unnormalized Fourier matrix over `ZMod d`, proves its orthogonality
identities, and uses Fourier conjugation to control diagonal entries. It constructs Hermitian
commutator factors for zero-diagonal matrices and proves
`exists_hermitian_commutator_of_trace_zero`, the trace-zero decomposition relevant to
[DawsonNielsen2006].

## Main statements

* `diag_zero_construction`: Every Hermitian matrix with zero diagonal is, after multiplication
  by `I`, a commutator of two Hermitian matrices.
* `exists_hermitian_commutator_of_trace_zero`: Every trace-zero Hermitian matrix on `ZMod d` is,
  after multiplication by `I`, a commutator of two Hermitian matrices, giving the algebraic
  decomposition used in [DawsonNielsen2006].

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.HermitianDecomposition

open Matrix

set_option autoImplicit false

variable {d : ℕ} [NeZero d]

/-- The unnormalized Fourier matrix with entry `stdAddChar (-(i*j))` on `ZMod d`. -/
noncomputable def fourierMat : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => ZMod.stdAddChar (-(i * j))

/-- Complex conjugation of the standard additive character at `a` equals its value at `-a`. -/
lemma stdAddChar_conj (a : ZMod d) :
    (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj]
  congr 1
  exact (AddChar.map_neg_eq_inv ZMod.toCircle a).symm

/-- The conjugate transpose of the unnormalized Fourier matrix multiplied by the matrix equals
`d` times the identity. -/
lemma fourierMat_orth : (fourierMat (d := d) : Matrix (ZMod d) (ZMod d) ℂ)ᴴ * fourierMat =
    (d : ℂ) • 1 := by
  ext i j
  simp only [fourierMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.one_apply]
  have hstep : ∀ k : ZMod d,
      star (ZMod.stdAddChar (-(k * i))) * ZMod.stdAddChar (-(k * j)) =
        ZMod.stdAddChar (k * (i - j)) := by
    intro k
    rw [show star (ZMod.stdAddChar (-(k * i))) =
        (starRingEnd ℂ) (ZMod.stdAddChar (-(k * i))) from rfl, stdAddChar_conj,
      ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hstep, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  by_cases h : i = j
  · subst h; simp
  · have hsub : i - j ≠ 0 := sub_ne_zero.mpr h
    simp [h, hsub]

/-- The unnormalized Fourier matrix multiplied by its conjugate transpose equals `d` times the
identity. -/
lemma fourierMat_orth' : (fourierMat (d := d) : Matrix (ZMod d) (ZMod d) ℂ) * fourierMatᴴ =
    (d : ℂ) • 1 := by
  ext i j
  simp only [fourierMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.one_apply]
  have hstep : ∀ k : ZMod d,
      ZMod.stdAddChar (-(i * k)) * star (ZMod.stdAddChar (-(j * k))) =
        ZMod.stdAddChar (k * (j - i)) := by
    intro k
    rw [show star (ZMod.stdAddChar (-(j * k))) =
        (starRingEnd ℂ) (ZMod.stdAddChar (-(j * k))) from rfl, stdAddChar_conj,
      ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hstep, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  by_cases h : j = i
  · subst h; simp
  · have hsub : j - i ≠ 0 := sub_ne_zero.mpr h
    have hij : i ≠ j := fun e => h e.symm
    simp [hsub, hij]

/-- Every entry of the unnormalized Fourier matrix has complex norm one. -/
lemma fourierMat_entry_norm (i j : ZMod d) : ‖fourierMat (d := d) i j‖ = 1 := by
  rw [fourierMat, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Each Fourier matrix entry multiplied by its complex conjugate equals one. -/
lemma mul_conj_entry (i j : ZMod d) :
    fourierMat (d := d) i j * star (fourierMat (d := d) i j) = 1 := by
  change fourierMat i j * (starRingEnd ℂ) (fourierMat i j) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, fourierMat_entry_norm]
  norm_num

/-- Every diagonal entry of the Fourier conjugation of a real diagonal matrix equals the sum of
its diagonal values. -/
lemma fourier_diag_conj (lam : ZMod d → ℝ) (i : ZMod d) :
    (((fourierMat : Matrix (ZMod d) (ZMod d) ℂ) * diagonal (fun j => (lam j : ℂ)) *
      ((fourierMat : Matrix (ZMod d) (ZMod d) ℂ)ᴴ))) i i = ∑ j, (lam j : ℂ) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  have hinner : ∀ x : ZMod d,
      (∑ x_1, (if x = x_1 then (lam x : ℂ) else 0) * star (fourierMat i x_1))
        = (lam x : ℂ) * star (fourierMat i x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ x) h
  simp only [hinner]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [show fourierMat i x * ((lam x : ℂ) * star (fourierMat i x))
      = (lam x : ℂ) * (fourierMat i x * star (fourierMat i x)) by ring,
    mul_conj_entry, mul_one]

/-- The real value of the canonical natural-number representative of an element of `ZMod d`. -/
noncomputable def gval (k : ZMod d) : ℝ := (k.val : ℝ)

/-- Distinct residue labels have distinct complex casts of their `gval` values. -/
lemma gval_sub_ne_zero {i j : ZMod d} (h : i ≠ j) :
    ((gval j : ℝ) : ℂ) - ((gval i : ℝ) : ℂ) ≠ 0 := by
  intro hz
  have hv : (j.val : ℝ) = (i.val : ℝ) := by
    have := sub_eq_zero.mp hz
    simpa [gval] using this
  have hv' : j.val = i.val := by exact_mod_cast hv
  exact h (ZMod.val_injective d hv').symm

omit [NeZero d] in

/-- The complex cast of `gval k` is fixed by complex conjugation. -/
lemma gval_star (k : ZMod d) : star (((gval k : ℝ)) : ℂ) = ((gval k : ℝ) : ℂ) := by
  simp

/-- Every Hermitian matrix with zero diagonal is, after multiplication by `I`, a commutator of
two Hermitian matrices. -/
theorem diag_zero_construction (A : Matrix (ZMod d) (ZMod d) ℂ) (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0) :
    ∃ F G : Matrix (ZMod d) (ZMod d) ℂ,
      F.IsHermitian ∧ G.IsHermitian ∧ F * G - G * F = Complex.I • A := by
  classical
  let F : Matrix (ZMod d) (ZMod d) ℂ :=
    fun i j => if i = j then 0 else Complex.I * A i j / (((gval j : ℝ) : ℂ) - ((gval i : ℝ) : ℂ))
  let G : Matrix (ZMod d) (ZMod d) ℂ := diagonal (fun k => ((gval k : ℝ) : ℂ))
  refine ⟨F, G, ?_, ?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [F, Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [if_neg hij, if_neg hji]
      rw [star_div₀, star_mul, star_sub]
      rw [hA.apply i j]
      have hI : star (Complex.I) = -Complex.I := by
        simp [RCLike.star_def]
      rw [hI]
      simp only [gval_star]
      have hd : (((gval j : ℝ)) : ℂ) - ((gval i : ℝ) : ℂ) ≠ 0 := gval_sub_ne_zero hij
      have hd2 : (((gval i : ℝ)) : ℂ) - ((gval j : ℝ) : ℂ) ≠ 0 := gval_sub_ne_zero hji
      field_simp [hd, hd2]
      ring
  · exact Matrix.isHermitian_diagonal_of_self_adjoint _ (funext gval_star)
  · ext i j
    have hFG : (F * G) i j = F i j * ((gval j : ℝ) : ℂ) := by
      simp only [G]
      rw [Matrix.mul_diagonal]
    have hGF : (G * F) i j = ((gval i : ℝ) : ℂ) * F i j := by
      simp only [G]
      rw [Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hFG, hGF]
    by_cases hij : i = j
    · subst hij
      rw [show F i i = 0 from by simp [F]]
      rw [hdiag i]
      ring
    · have hd : (((gval j : ℝ)) : ℂ) - ((gval i : ℝ) : ℂ) ≠ 0 := gval_sub_ne_zero hij
      rw [show F i j = Complex.I * A i j / (((gval j : ℝ) : ℂ) - ((gval i : ℝ) : ℂ)) from by
        simp [F, hij]]
      field_simp [hd]

/-- Every trace-zero Hermitian matrix on `ZMod d` is, after multiplication by `I`, a commutator
of two Hermitian matrices, giving the algebraic decomposition used in [DawsonNielsen2006]. -/
theorem exists_hermitian_commutator_of_trace_zero
    (H : Matrix (ZMod d) (ZMod d) ℂ) (hH : H.IsHermitian) (htr : H.trace = 0) :
    ∃ F G : Matrix (ZMod d) (ZMod d) ℂ,
      F.IsHermitian ∧ G.IsHermitian ∧ F * G - G * F = Complex.I • H := by
  classical
  let U : Matrix (ZMod d) (ZMod d) ℂ := hH.eigenvectorUnitary
  let lam : ZMod d → ℝ := hH.eigenvalues
  let D : Matrix (ZMod d) (ZMod d) ℂ := diagonal (fun i => ((lam i : ℝ) : ℂ))
  have hspec : H = U * D * Uᴴ := by
    have := hH.spectral_theorem
    simpa [U, D, lam, RCLike.ofReal] using! this
  have hU : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUr : U * Uᴴ = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using!
      Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have htrD : H.trace = ∑ i, ((lam i : ℝ) : ℂ) := by
    rw [hspec, Matrix.trace_mul_comm (U * D) Uᴴ, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    simp [D]
  let Q0 : Matrix (ZMod d) (ZMod d) ℂ := fourierMat * Uᴴ
  have hQ0l : Q0ᴴ * Q0 = (d : ℂ) • 1 := by
    simp only [Q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (U * fourierMatᴴ) * (fourierMat * Uᴴ)
        = U * (fourierMatᴴ * fourierMat) * Uᴴ := by noncomm_ring
      _ = U * ((d : ℂ) • 1) * Uᴴ := by rw [fourierMat_orth]
      _ = (d : ℂ) • (U * Uᴴ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (d : ℂ) • 1 := by rw [hUr]
  have hQ0r : Q0 * Q0ᴴ = (d : ℂ) • 1 := by
    simp only [Q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (fourierMat * Uᴴ) * (U * fourierMatᴴ)
        = fourierMat * (Uᴴ * U) * fourierMatᴴ := by noncomm_ring
      _ = fourierMat * 1 * fourierMatᴴ := by rw [hU]
      _ = fourierMat * fourierMatᴴ := by simp
      _ = (d : ℂ) • 1 := fourierMat_orth'
  let H' : Matrix (ZMod d) (ZMod d) ℂ := Q0 * H * Q0ᴴ
  have hH'diag : H' = fourierMat * D * fourierMatᴴ := by
    simp only [H', Q0, hspec, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (fourierMat * Uᴴ) * (U * D * Uᴴ) * (U * fourierMatᴴ)
        = fourierMat * (Uᴴ * U) * D * (Uᴴ * U) * fourierMatᴴ := by noncomm_ring
      _ = fourierMat * 1 * D * 1 * fourierMatᴴ := by rw [hU]
      _ = fourierMat * D * fourierMatᴴ := by simp
  have hH'herm : H'.IsHermitian := by
    rw [Matrix.IsHermitian]
    simp only [H', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hH]
    noncomm_ring
  have hdiagH' : ∀ i, H' i i = 0 := by
    intro i
    rw [hH'diag, fourier_diag_conj (d := d) lam i]
    rw [← htrD, htr]
  obtain ⟨P, S, hP, hS, hPS⟩ := diag_zero_construction H' hH'herm hdiagH'
  let A : Matrix (ZMod d) (ZMod d) ℂ := Q0ᴴ * P * Q0
  let B : Matrix (ZMod d) (ZMod d) ℂ := Q0ᴴ * S * Q0
  have hA : A.IsHermitian := by
    rw [Matrix.IsHermitian] at hP ⊢
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP]
    noncomm_ring
  have hB : B.IsHermitian := by
    rw [Matrix.IsHermitian] at hS ⊢
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS]
    noncomm_ring
  have hQ0H : Q0ᴴ * H' * Q0 = (d : ℂ) ^ 2 • H := by
    simp only [H']
    calc Q0ᴴ * (Q0 * H * Q0ᴴ) * Q0
        = (Q0ᴴ * Q0) * H * (Q0ᴴ * Q0) := by noncomm_ring
      _ = ((d : ℂ) • 1) * H * ((d : ℂ) • 1) := by rw [hQ0l]
      _ = (d : ℂ) ^ 2 • H := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
            smul_smul]
          rw [← pow_two]
  have hAB : A * B - B * A = Complex.I • ((d : ℂ) ^ 3 • H) := by
    simp only [A, B]
    calc (Q0ᴴ * P * Q0) * (Q0ᴴ * S * Q0) - (Q0ᴴ * S * Q0) * (Q0ᴴ * P * Q0)
        = (Q0ᴴ * P) * (Q0 * Q0ᴴ) * (S * Q0) - (Q0ᴴ * S) * (Q0 * Q0ᴴ) * (P * Q0) := by
            noncomm_ring
      _ = (Q0ᴴ * P) * ((d : ℂ) • 1) * (S * Q0) - (Q0ᴴ * S) * ((d : ℂ) • 1) * (P * Q0) := by
            rw [hQ0r]
      _ = (d : ℂ) • (Q0ᴴ * (P * S - S * P) * Q0) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
            rw [← smul_sub]
            congr 1
            noncomm_ring
      _ = (d : ℂ) • (Q0ᴴ * (Complex.I • H') * Q0) := by rw [hPS]
      _ = (d : ℂ) • (Complex.I • (Q0ᴴ * H' * Q0)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = (d : ℂ) • (Complex.I • ((d : ℂ) ^ 2 • H)) := by rw [hQ0H]
      _ = Complex.I • ((d : ℂ) ^ 3 • H) := by
            have hs : (d : ℂ) * (Complex.I * (d : ℂ) ^ 2) = Complex.I * (d : ℂ) ^ 3 := by
              ring
            simp only [smul_smul]
            rw [hs]
  let c : ℝ := ((d : ℝ) ^ 3)⁻¹
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hcdef : (c : ℂ) = ((d : ℂ) ^ 3)⁻¹ := by
    simp [c]
  have hc : (c : ℂ) * (d : ℂ) ^ 3 = 1 := by
    rw [hcdef, inv_mul_cancel₀ (pow_ne_zero 3 hdC)]
  refine ⟨(c : ℂ) • A, B, ?_, hB, ?_⟩
  · rw [Matrix.IsHermitian] at hA ⊢
    simp only [Matrix.conjTranspose_smul, hA]
    congr 1
    rw [RCLike.star_def]
    exact (Complex.conj_ofReal c).symm ▸ rfl
  · calc ((c : ℂ) • A) * B - B * ((c : ℂ) • A)
        = (c : ℂ) • (A * B - B * A) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      _ = (c : ℂ) • (Complex.I • ((d : ℂ) ^ 3 • H)) := by rw [hAB]
      _ = Complex.I • H := by
            have hI : (c : ℂ) * (Complex.I * (d : ℂ) ^ 3) = Complex.I := by
              calc (c : ℂ) * (Complex.I * (d : ℂ) ^ 3)
                  = Complex.I * ((c : ℂ) * (d : ℂ) ^ 3) := by ring
                _ = Complex.I := by rw [hc, mul_one]
            simp only [smul_smul]
            rw [hI]

end Qatlib.Papers.SolovayKitaev05.MainResults.HermitianDecomposition
