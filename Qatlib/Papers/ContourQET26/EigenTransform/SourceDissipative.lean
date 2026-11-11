/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option backward.isDefEq.respectTransparency false

/-!
# Dissipative condition versus eigenvalue real parts

Source: Jiang and An, "Contour-integral based quantum eigenvalue transformation: analysis and
applications", fixed arXiv:2601.11959v3 (2026-09-20).

Appendix B (Lemma 11, p. 34) proves that `A + A† ⪯ 0` implies `Re λ ≤ 0` for every eigenvalue
`λ` of `A`, and that the converse fails.  The statement is formalized with the complex
quadratic-form predicate `NegSemidefQF` for the negative-semidefinite hypothesis (Mathlib's
`Matrix.PosSemidef` is stated over ordered star rings, which excludes `ℂ`), and with an
explicit eigenpair `A *ᵥ v = lam • v`, `v ≠ 0`.  The counterexample is the nilpotent matrix
`!![0, 1; 0, 0]`.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.ContourQET26.EigenTransform

/-- Auxiliary computation: `v† v` is the real number `∑ ‖v i‖²`. -/
lemma star_dotProduct_self_eq_ofReal_sum_normSq {N : ℕ} (v : Fin N → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ =>
    show star v i * v i = ((Complex.normSq (v i) : ℝ) : ℂ) by
      rw [Complex.normSq_apply, Complex.ext_iff]
      constructor <;> simp <;> ring

/-- Complex Loewner negative semidefiniteness in quadratic-form form: `-(A + A†)` has
nonnegative real quadratic form on every vector.  This is the complex counterpart of the
paper's `A + A† ⪯ 0`. -/
def NegSemidefQF {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ v : Fin N → ℂ, 0 ≤ (star v ⬝ᵥ ((-(A + Aᴴ)) *ᵥ v)).re

/-- Source Lemma 11 (p. 34), forward direction.  If `A + A†` is negative semi-definite then every
eigenvalue of `A` has non-positive real part.  The proof is the paper's: multiply
`A + A† ⪯ 0` by the eigenvector and use `v† A v = lam ‖v‖²`. -/
theorem lemma11_re_nonpos {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : NegSemidefQF A) {lam : ℂ} {v : Fin N → ℂ}
    (hv : v ≠ 0) (heig : A *ᵥ v = lam • v) : lam.re ≤ 0 := by
  classical
  set s : ℂ := star v ⬝ᵥ v with hs
  have hsR : s = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [hs]
    exact star_dotProduct_self_eq_ofReal_sum_normSq v
  have hsim : s.im = 0 := by
    rw [hsR]
    simp
  have hspos : 0 < s.re := by
    rw [hsR, Complex.ofReal_re]
    refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (v i)) ?_
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv (funext hall)
    exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  have hAterm : star v ⬝ᵥ (A *ᵥ v) = lam * s := by
    rw [heig, dotProduct_smul, ← hs, smul_eq_mul]
  have hstarA : star (Aᴴ *ᵥ v) = star v ᵥ* A := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hconjS : star s = s := by
    rw [hsR]
    simp
  have hAadj : star v ⬝ᵥ (Aᴴ *ᵥ v) = (star lam) * s := by
    calc star v ⬝ᵥ (Aᴴ *ᵥ v)
        = star v ⬝ᵥ star (star (Aᴴ *ᵥ v)) := by rw [star_star]
      _ = star (star (Aᴴ *ᵥ v) ⬝ᵥ v) := star_dotProduct_star _ _
      _ = star ((star v ᵥ* A) ⬝ᵥ v) := by rw [hstarA]
      _ = star (star v ⬝ᵥ (A *ᵥ v)) := by rw [dotProduct_mulVec]
      _ = star (lam * s) := by rw [hAterm]
      _ = star s * star lam := by rw [star_mul]
      _ = s * star lam := by rw [hconjS]
      _ = star lam * s := by rw [mul_comm]
  have hform : star v ⬝ᵥ ((-(A + Aᴴ)) *ᵥ v) = -(lam * s) + -((star lam) * s) := by
    rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.add_mulVec, dotProduct_add,
      hAterm, hAadj]
    ring
  have hstarre : (star lam).re = lam.re := by
    rw [Complex.star_def]; simp
  have hre : (star v ⬝ᵥ ((-(A + Aᴴ)) *ᵥ v)).re = -2 * (lam.re * s.re) := by
    rw [hform]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, hsim,
      mul_zero, sub_zero]
    rw [hstarre]
    ring
  have hnonneg : 0 ≤ (star v ⬝ᵥ ((-(A + Aᴴ)) *ᵥ v)).re := hA v
  rw [hre] at hnonneg
  have hprod : lam.re * s.re ≤ 0 := by nlinarith
  by_contra h
  push_neg at h
  have hlt : 0 < lam.re * s.re := mul_pos h hspos
  linarith

/-- The nilpotent counterexample from Lemma 11 (p. 34): `!![0,1;0,0]`. -/
def nilpotentCounterexample : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Source Lemma 11 (p. 34), counterexample.  The matrix `!![0,1;0,0]` has all eigenvalues equal
to `0` (non-positive real part), but `A + A†` is not negative semi-definite. -/
theorem lemma11_converse_counterexample :
    (∀ lam : ℂ, (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ nilpotentCounterexample *ᵥ v = lam • v) →
      lam.re ≤ 0) ∧
    ¬ NegSemidefQF nilpotentCounterexample := by
  constructor
  · rintro lam ⟨v, hv, heig⟩
    have hsq : nilpotentCounterexample * nilpotentCounterexample = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [nilpotentCounterexample, Matrix.mul_apply, Fin.sum_univ_two]
    have hlam2 : lam * lam = 0 := by
      have h : (nilpotentCounterexample * nilpotentCounterexample) *ᵥ v = lam • (lam • v) := by
        rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig]
      rw [hsq, Matrix.zero_mulVec] at h
      have h' : (lam * lam) • v = 0 := by
        simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h.symm
      exact (smul_eq_zero.mp h').resolve_right hv
    have hlam : lam = 0 := by
      rcases mul_eq_zero.mp hlam2 with h | h <;> exact h
    subst hlam
    simp
  · intro hPSD
    let v : Fin 2 → ℂ := ![1, 1]
    have hnn := hPSD v
    have hval : (star v ⬝ᵥ ((-(nilpotentCounterexample + nilpotentCounterexampleᴴ)) *ᵥ v)).re
        = -2 := by
      norm_num [v, nilpotentCounterexample, dotProduct, Matrix.mulVec, Matrix.add_apply,
        Matrix.neg_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    rw [hval] at hnn
    norm_num at hnn

end Qatlib.Papers.ContourQET26.EigenTransform
