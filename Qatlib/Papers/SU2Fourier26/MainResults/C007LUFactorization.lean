/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceCoefficientOps

/-!
# Lemma 3: the LU factorization of `C` and its triangularity (c007)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 3, (3.3)–(3.4), p.9.

With

`C = [[1, b*/a], [-b/a*, 1]]`,
`L = [[1/a, b*/a], [0, 1]]`,  `U = [[1/a*, 0], [-b/a*, 1]]`,
`L̃ = [[1, b*/a], [0, 1/a]]`,  `Ũ = [[1, 0], [-b/a*, 1/a*]]`,

the paper proves `C = L U = Ũ L̃` using only `|a|² + |b|² = 1` ((3.3)), and then
the annihilation identities `R̃ₙ L̃ Pₙ = R̃ₙ L̃⁻¹ Pₙ = Pₙ Ũ R̃ₙ = Pₙ Ũ⁻¹ R̃ₙ = 0`
((3.4)), whose only non-trivial entries reduce to the Fourier-support fact that
`1/a` (resp. `a`) is supported on `(-∞, 0]` and `1/a*` (resp. `a*`) on `[0, +∞)`.
-/

open scoped BigOperators Matrix
open Matrix MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- The matrix `C = [[1, b*/a], [-b/a*, 1]]` of (3.3), p.8–9. -/
def Cmat (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, starFun b x / a x; -(b x / starFun a x), 1]

/-- The lower-triangular factor `L = [[1/a, b*/a], [0, 1]]` of (3.3), p.9. -/
def Lmat (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a x)⁻¹, starFun b x / a x; 0, 1]

/-- The upper-triangular factor `U = [[1/a*, 0], [-b/a*, 1]]` of (3.3), p.9. -/
def Umat (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(starFun a x)⁻¹, 0; -(b x / starFun a x), 1]

/-- The lower-triangular factor `L̃ = [[1, b*/a], [0, 1/a]]` of (3.3), p.9. -/
def LtilMat (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, starFun b x / a x; 0, (a x)⁻¹]

/-- The upper-triangular factor `Ũ = [[1, 0], [-b/a*, 1/a*]]` of (3.3), p.9. -/
def UtilMat (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; -(b x / starFun a x), (starFun a x)⁻¹]

/-- `a x * starFun a x ≠ 0` under the standing hypotheses (from `|a|² + |b|² = 1`
and `‖b‖_∞ < 1`, p.6). -/
theorem mul_star_ne_zero {W : StrongBeurlingWeight} {a b : CircleT → ℂ}
    (h : OuterSetup W a b) (x : CircleT) : a x * starFun a x ≠ 0 := by
  intro hz
  have hunit := h.unit x
  rw [hz, zero_add] at hunit
  have hnorm : ‖b x * starFun b x‖ < 1 := by
    rw [norm_mul]
    have hbx := h.small_b x
    have hbnx := h.small_b (-x)
    have hs : starFun b x = b (-x) := rfl
    rw [hs]
    nlinarith [norm_nonneg (b x), norm_nonneg (b (-x))]
  rw [hunit] at hnorm
  simpa using hnorm

/-- `a x ≠ 0` under the standing hypotheses. -/
theorem a_ne_zero {W : StrongBeurlingWeight} {a b : CircleT → ℂ}
    (h : OuterSetup W a b) (x : CircleT) : a x ≠ 0 :=
  left_ne_zero_of_mul (mul_star_ne_zero h x)

/-- `a* x ≠ 0` under the standing hypotheses. -/
theorem starFun_a_ne_zero {W : StrongBeurlingWeight} {a b : CircleT → ℂ}
    (h : OuterSetup W a b) (x : CircleT) : starFun a x ≠ 0 :=
  right_ne_zero_of_mul (mul_star_ne_zero h x)

/-- Lemma 3, equation (3.3) of arXiv:2603.02021v1, p.9: `C = L U = Ũ L̃`
pointwise on `𝕋`, using only `|a|² + |b|² = 1`. -/
theorem lu_factorization (W : StrongBeurlingWeight) (a b : CircleT → ℂ)
    (h : OuterSetup W a b) :
    (∀ x : CircleT, Cmat a b x = Lmat a b x * Umat a b x) ∧
      ∀ x : CircleT, Cmat a b x = UtilMat a b x * LtilMat a b x := by
  constructor
  · intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Cmat, Lmat, Umat, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      first
      | (field_simp [mul_star_ne_zero h x, a_ne_zero h x, starFun_a_ne_zero h x]
         linear_combination h.unit x)
      | ring
      | linear_combination h.unit x
  · intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Cmat, UtilMat, LtilMat, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      first
      | (field_simp [mul_star_ne_zero h x, a_ne_zero h x, starFun_a_ne_zero h x]
         linear_combination h.unit x)
      | ring
      | linear_combination h.unit x

/-- Lemma 3, equation (3.4) of arXiv:2603.02021v1, p.9, in its coefficient form:
multiplying by `1/a` or by `a` (Fourier support in `(-∞, 0]`) preserves the
Fourier support bound `(-∞, n]`, and multiplying by `1/a*` or by `a*` (support in
`[0, +∞)`) preserves support in `(n, +∞)`.  These four support statements are
exactly the four operator identities `R̃ₙ L̃ Pₙ = R̃ₙ L̃⁻¹ Pₙ = Pₙ Ũ R̃ₙ =
Pₙ Ũ⁻¹ R̃ₙ = 0`, whose non-zero matrix entries are `1/a`, `a`, `1/a*`, `a*`
(the remaining entries are the identically-zero entries of `L̃`, `L̃⁻¹`, `Ũ`,
`Ũ⁻¹` or the diagonal `1` with support `{0} ⊆ (-∞, 0]`). -/
theorem projection_annihilation (W : StrongBeurlingWeight) (a b : CircleT → ℂ)
    (h : OuterSetup W a b) (n : ℤ) :
    (∀ g : ℤ → ℂ, SupportedLE g n → ∀ j : ℤ, n < j →
        convCoeff (coeffs fun x => (a x)⁻¹) g j = 0) ∧
      (∀ g : ℤ → ℂ, SupportedLE g n → ∀ j : ℤ, n < j →
        convCoeff (coeffs a) g j = 0) ∧
      (∀ g : ℤ → ℂ, SupportedGT g n → ∀ j : ℤ, j ≤ n →
        convCoeff (coeffs (starFun a)) g j = 0) ∧
      (∀ g : ℤ → ℂ, SupportedGT g n → ∀ j : ℤ, j ≤ n →
        convCoeff (coeffs fun x => (starFun a x)⁻¹) g j = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg j hj
    exact convCoeff_eq_zero_of_supported_le
      (fun k hk => h.inv_a_support k hk) hg hj
  · intro g hg j hj
    exact convCoeff_eq_zero_of_supported_le
      (fun k hk => h.a_support k hk) hg hj
  · intro g hg j hj
    exact convCoeff_eq_zero_of_supported_ge
      (fun k hk => h.aStar_support k hk) hg hj
  · intro g hg j hj
    exact convCoeff_eq_zero_of_supported_ge
      (fun k hk => h.inv_aStar_support k hk) hg hj

end

end Qatlib.Papers.SU2Fourier26.MainResults
