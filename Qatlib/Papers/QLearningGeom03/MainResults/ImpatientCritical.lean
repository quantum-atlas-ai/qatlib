/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Critical points of the impatient learning objective

This module studies the first variation of the diagonal squared norm `diagNormSq` in
skew-Hermitian directions. The predicate `IsOrbitCritical` requires these derivatives to vanish
and is characterized by Hermiticity of `B * (diagProj B)ᴴ`.

For Hermitian `B`, criticality is equivalent to commutation with its diagonal projection. These
statements formalize Proposition 3.1 and Corollary 3.2 of [HunzikerEtAl2003].

## Main statements

* `hasDerivAt_diagNormSq_unitPath`: The first-variation formula for the diagonal objective.
* `critical_iff_hermitian`: Criticality characterized by a Hermitian matrix product.
* `hermitian_critical_iff_commutes_diag`: The commutation criterion for Hermitian matrices.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {n : ℕ}

/-- The diagonal matrix whose diagonal entries agree with those of `B`. -/
def diagProj (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => B i i

/-- The sum of the squared complex norms of the diagonal entries of `B`. -/
noncomputable def diagNormSq (B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, Complex.normSq (B i i)

/-- The predicate that the conjugate transpose of a matrix is its negative. -/
def IsSkewHermitian (A : Matrix (Fin n) (Fin n) ℂ) : Prop := Aᴴ = -A

/-- Diagonal projection commutes with conjugate transpose. -/
lemma diagProj_conjTranspose (B : Matrix (Fin n) (Fin n) ℂ) :
    (diagProj B)ᴴ = diagProj Bᴴ := by
  unfold diagProj
  rw [Matrix.diagonal_conjTranspose]
  simp [Matrix.conjTranspose_apply]

/-- Multiplication by `1 + t • ζ` expands as `B + t • (ζ * B)`. -/
lemma unitPath_mul (t : ℝ) (ζ B : Matrix (Fin n) (Fin n) ℂ) :
    (1 + t • ζ) * B = B + t • (ζ * B) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]

/-- The derivative at zero of the squared norm of `c + t • d` is twice the real part of c times
the conjugate of d. -/
lemma hasDerivAt_normSq_add_smul (c d : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.normSq (c + t • d)) (2 * (c * star d).re) 0 := by
  have hpoly : ∀ t : ℝ,
      Complex.normSq (c + t • d)
        = Complex.normSq c + 2 * t * (c * star d).re + t ^ 2 * Complex.normSq d := by
    intro t
    rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.real_smul,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hfun : (fun t : ℝ => Complex.normSq (c + t • d))
      = fun t : ℝ =>
        Complex.normSq c + 2 * t * (c * star d).re + t ^ 2 * Complex.normSq d :=
    funext hpoly
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => 2 * t * (c * star d).re) (2 * (c * star d).re) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (2 * (c * star d).re)
    simpa only [id, one_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * Complex.normSq d) (2 * 0 * Complex.normSq d) 0 := by
    have h := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (Complex.normSq d)
    simpa using h
  have h3 : HasDerivAt (fun _ : ℝ => Complex.normSq c) 0 0 := hasDerivAt_const _ _
  have h4 := (h3.add h1).add h2
  simpa using! h4

/-- The trace pairing of the conjugate transpose of `diagProj B` with `X` is the sum of the
corresponding diagonal-entry products. -/
lemma trace_diagProj_conjTranspose_mul (B X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((diagProj B)ᴴ * X) = ∑ i, star (B i i) * X i i := by
  unfold diagProj
  rw [Matrix.diagonal_conjTranspose, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by simp [Matrix.diagonal_mul]

/-- The sum of the real parts of the diagonal products Bᵢᵢ times the conjugate of Xᵢᵢ is the
real part of the diagonal-projection trace pairing. -/
lemma sum_mul_conj_re_eq_trace_re (B X : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, (B i i * star (X i i)).re) = (Matrix.trace ((diagProj B)ᴴ * X)).re := by
  rw [trace_diagProj_conjTranspose_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The derivative at zero of `diagNormSq ((1 + t • ζ) * B)` is twice the real part of the trace
of `(diagProj B)ᴴ * (ζ * B)`. -/
lemma hasDerivAt_diagNormSq_unitPath (B ζ : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => diagNormSq ((1 + t • ζ) * B))
      (2 * (Matrix.trace ((diagProj B)ᴴ * (ζ * B))).re) 0 := by
  have hfun : (fun t : ℝ => diagNormSq ((1 + t • ζ) * B))
      = fun t : ℝ => ∑ i, Complex.normSq (B i i + t • ((ζ * B) i i)) := by
    funext t
    rw [diagNormSq, unitPath_mul]
    simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [hfun]
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, Complex.normSq (B i i + t • ((ζ * B) i i)))
      (∑ i, 2 * (B i i * star ((ζ * B) i i)).re) 0 := by
    have h := HasDerivAt.sum
      (u := Finset.univ) (fun i _ => hasDerivAt_normSq_add_smul (B i i) ((ζ * B) i i))
    have h' : (∑ i, (fun t : ℝ => Complex.normSq (B i i + t • ((ζ * B) i i))))
        = fun t : ℝ => ∑ i, Complex.normSq (B i i + t • ((ζ * B) i i)) := by
      funext t
      simp
    simpa only [h'] using h
  have hval : (∑ i, 2 * (B i i * star ((ζ * B) i i)).re)
      = 2 * (Matrix.trace ((diagProj B)ᴴ * (ζ * B))).re := by
    rw [← sum_mul_conj_re_eq_trace_re, Finset.mul_sum]
  simpa only [hval] using hsum

/-- A complex number whose conjugate equals its negative has zero real part. -/
lemma re_eq_zero_of_star_eq_neg {z : ℂ} (h : star z = -z) : z.re = 0 := by
  have h' := congrArg Complex.re h
  simp at h'
  linarith

/-- The trace of a skew-Hermitian matrix has zero real part. -/
lemma trace_re_eq_zero_of_isSkewHermitian {X : Matrix (Fin n) (Fin n) ℂ}
    (h : IsSkewHermitian X) : (Matrix.trace X).re = 0 := by
  refine re_eq_zero_of_star_eq_neg ?_
  rw [← Matrix.trace_conjTranspose, h, Matrix.trace_neg]

/-- The trace of `Aᴴ * A` is the sum of the squared complex norms of the entries of `A`,
embedded in the complex numbers. -/
lemma trace_conjTranspose_mul_self (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Aᴴ * A) = ((∑ i, ∑ j, Complex.normSq (A j i) : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Swapping the row and column indices in the double sum of squared entry norms leaves the sum
unchanged. -/
lemma normSq_sum_swap (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, Complex.normSq (A j i)) = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [Finset.sum_comm]

/-- A complex matrix is zero if the trace of `Aᴴ * A` is zero. -/
lemma eq_zero_of_trace_conjTranspose_mul_self {A : Matrix (Fin n) (Fin n) ℂ}
    (h : Matrix.trace (Aᴴ * A) = 0) : A = 0 := by
  have hreal : (∑ i, ∑ j, Complex.normSq (A i j) : ℝ) = 0 := by
    rw [trace_conjTranspose_mul_self] at h
    have h' : (∑ i, ∑ j, Complex.normSq (A j i) : ℝ) = 0 := Complex.ofReal_eq_zero.mp h
    rwa [normSq_sum_swap] at h'
  have hnn : ∀ i j, 0 ≤ Complex.normSq (A i j) := fun i j => Complex.normSq_nonneg _
  have hinner : ∀ i, ∑ j, Complex.normSq (A i j) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).mp hreal
    exact fun i => this i (Finset.mem_univ i)
  ext i j
  have hzero : Complex.normSq (A i j) = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp (hinner i)
    exact h j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hzero

/-- The skew part `(M - Mᴴ) / 2` is skew-Hermitian. -/
lemma isSkewHermitian_skewPart (M : Matrix (Fin n) (Fin n) ℂ) :
    IsSkewHermitian ((2 : ℂ)⁻¹ • (M - Mᴴ)) := by
  unfold IsSkewHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  rw [show star (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ by norm_num]
  rw [show Mᴴ - M = -(M - Mᴴ) by abel, smul_neg]

/-- The Hermitian part `(M + Mᴴ) / 2` is Hermitian. -/
lemma isHermitian_hermitianPart (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.IsHermitian ((2 : ℂ)⁻¹ • (M + Mᴴ)) := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [show star (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ by norm_num, add_comm]

/-- A matrix `M` is Hermitian exactly when the real part of `trace (ζ * M)` vanishes for every
skew-Hermitian `ζ`. This gives the trace criterion used in [Hunziker et al., Proposition
3.1][HunzikerEtAl2003]. -/
theorem forall_trace_re_eq_zero_iff_isHermitian (M : Matrix (Fin n) (Fin n) ℂ) :
    (∀ ζ, IsSkewHermitian ζ → (Matrix.trace (ζ * M)).re = 0) ↔ Matrix.IsHermitian M := by
  constructor
  · intro h
    set H : Matrix (Fin n) (Fin n) ℂ := (2 : ℂ)⁻¹ • (M + Mᴴ) with hHdef
    set S : Matrix (Fin n) (Fin n) ℂ := (2 : ℂ)⁻¹ • (M - Mᴴ) with hSdef
    have hH : Matrix.IsHermitian H := isHermitian_hermitianPart M
    have hS : IsSkewHermitian S := isSkewHermitian_skewPart M
    have hS' : Sᴴ = -S := hS
    have hH' : Hᴴ = H := hH
    have hM : M = H + S := by
      rw [hHdef, hSdef, ← smul_add]
      have hsum : M + Mᴴ + (M - Mᴴ) = M + M := by abel
      rw [hsum]
      have h2 : M + M = (2 : ℂ) • M := by rw [two_smul]
      rw [h2, smul_smul]
      simp
    have hcrit := h S hS
    rw [hM, Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hcrit
    have hSH : (Matrix.trace (S * H)).re = 0 := by
      refine re_eq_zero_of_star_eq_neg ?_
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH', hS']
      rw [show H * -S = -(H * S) by rw [mul_neg], Matrix.trace_neg,
        Matrix.trace_mul_comm H S]
    have hSS : Matrix.trace (S * S) = -Matrix.trace (Sᴴ * S) := by
      rw [hS', Matrix.neg_mul, Matrix.trace_neg]
      ring
    have hSSre : (Matrix.trace (S * S)).re = -(∑ i, ∑ j, Complex.normSq (S i j)) := by
      rw [hSS, Complex.neg_re, trace_conjTranspose_mul_self, Complex.ofReal_re,
        normSq_sum_swap]
    have hsumzero : (∑ i, ∑ j, Complex.normSq (S i j)) = 0 := by linarith
    have hSz : S = 0 := by
      refine eq_zero_of_trace_conjTranspose_mul_self ?_
      rw [trace_conjTranspose_mul_self, normSq_sum_swap, hsumzero]
      simp
    rw [hM, hSz, add_zero]
    exact hH
  · intro hM ζ hζ
    refine re_eq_zero_of_star_eq_neg ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hζ, hM]
    rw [show M * -ζ = -(M * ζ) by rw [mul_neg], Matrix.trace_neg,
      Matrix.trace_mul_comm M ζ]

/-- The predicate that the diagonal squared norm has derivative zero at t = 0 along every
variation `(1 + t • ζ) * B` with skew-Hermitian `ζ`. -/
def IsOrbitCritical (B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ ζ, IsSkewHermitian ζ → HasDerivAt (fun t : ℝ => diagNormSq ((1 + t • ζ) * B)) 0 0

/-- The diagonal objective is critical in every skew-Hermitian direction exactly when `B *
(diagProj B)ᴴ` is Hermitian, as in [Hunziker et al., Proposition 3.1][HunzikerEtAl2003]. -/
theorem critical_iff_hermitian (B : Matrix (Fin n) (Fin n) ℂ) :
    IsOrbitCritical B ↔ Matrix.IsHermitian (B * (diagProj B)ᴴ) := by
  have hcyc : ∀ ζ : Matrix (Fin n) (Fin n) ℂ,
      Matrix.trace ((diagProj B)ᴴ * (ζ * B)) = Matrix.trace (ζ * (B * (diagProj B)ᴴ)) := by
    intro ζ
    rw [Matrix.trace_mul_comm, mul_assoc]
  constructor
  · intro hc
    rw [← forall_trace_re_eq_zero_iff_isHermitian]
    intro ζ hζ
    rw [← hcyc ζ]
    have h0 := hc ζ hζ
    have huniq := (hasDerivAt_diagNormSq_unitPath B ζ).unique h0
    linarith
  · intro hM ζ hζ
    have htr : (Matrix.trace (ζ * (B * (diagProj B)ᴴ))).re = 0 :=
      (forall_trace_re_eq_zero_iff_isHermitian _).mpr hM ζ hζ
    rw [← hcyc ζ] at htr
    have hz : 2 * (Matrix.trace ((diagProj B)ᴴ * (ζ * B))).re = 0 := by
      rw [htr]; ring
    simpa only [hz] using hasDerivAt_diagNormSq_unitPath B ζ

/-- For Hermitian `B`, criticality of the diagonal objective is equivalent to commutation of `B`
with `diagProj B`, as in [Hunziker et al., Corollary 3.2][HunzikerEtAl2003]. -/
theorem hermitian_critical_iff_commutes_diag (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : Matrix.IsHermitian B) :
    IsOrbitCritical B ↔ B * diagProj B = diagProj B * B := by
  rw [critical_iff_hermitian]
  have hB' : Bᴴ = B := hB
  have hd : (diagProj B)ᴴ = diagProj B := by rw [diagProj_conjTranspose, hB']
  have hrhs : (B * diagProj B)ᴴ = diagProj B * B := by
    rw [Matrix.conjTranspose_mul, hd, hB']
  show (B * (diagProj B)ᴴ)ᴴ = B * (diagProj B)ᴴ ↔ _
  rw [hd, hrhs]
  exact ⟨Eq.symm, Eq.symm⟩

/-- For a Hermitian matrix `B` satisfying `B * B = G`, criticality is equivalent to commutation
with its diagonal projection. This is the square-root formulation of [Hunziker et al.,
Corollary 3.2][HunzikerEtAl2003]. -/
theorem gram_sqrt_critical_iff_commutes_diag (G B : Matrix (Fin n) (Fin n) ℂ)
    (hB : Matrix.IsHermitian B) (_hG : B * B = G) :
    IsOrbitCritical B ↔ B * diagProj B = diagProj B * B :=
  hermitian_critical_iff_commutes_diag B hB

end Qatlib.Papers.QLearningGeom03.MainResults
