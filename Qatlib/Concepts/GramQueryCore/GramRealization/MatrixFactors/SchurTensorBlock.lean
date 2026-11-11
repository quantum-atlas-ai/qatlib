/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A three-dimensional Schur block estimate

This module defines the parameterized matrix `q1SchurBlock` and expands its real quadratic form
as a weighted sum of squared complex norms. Under nonnegative `t₁` and `t₂` with positive sum
and `s₁, s₂ ≥ 3`, the expansion gives the lower bound in `q1_schur_lower`; see [Bhatia2007] for
the surrounding matrix positivity methods.

## Main statements

* `q1_schur_quadratic_sos`: When `t₁ + t₂` is nonzero, the real quadratic form of `q1SchurBlock`
  expands into the stated weighted sum of six squared complex norms.

* `q1_schur_lower`: For nonnegative `t₁` and `t₂` with positive sum and `s₁, s₂ ≥ 3`, the real
  quadratic form of `q1SchurBlock` is at least three times the total squared coordinate norm.

## References

* [Bhatia, 2007][Bhatia2007]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.GramQueryCore.GramRealization.SchurTensorBlock

open Matrix

/-- The real-entry complex matrix of size three defined by the six parameters and the Schur
correction with denominator `t₁ + t₂`. -/
noncomputable def q1SchurBlock (t₁ t₂ r₁ r₂ s₁ s₂ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let T := t₁ + t₂
  let b₁ := t₁ * r₁
  let b₂ := t₂ * r₂
  let d₁ := s₁ + t₁ * r₁ ^ 2
  let d₂ := s₂ + t₂ * r₂ ^ 2
  !![((t₁+d₂-b₂^2/T : ℝ) : ℂ), ((-b₂*b₁/T : ℝ) : ℂ), (b₁ : ℂ);
     ((-b₁*b₂/T : ℝ) : ℂ), ((d₁+t₂-b₁^2/T : ℝ) : ℂ), (b₂ : ℂ);
     (b₁ : ℂ), (b₂ : ℂ), ((d₁+d₂ : ℝ) : ℂ)]

/-- When `t₁ + t₂` is nonzero, the real quadratic form of `q1SchurBlock` expands into the stated
weighted sum of six squared complex norms. -/
theorem q1_schur_quadratic_sos (t₁ t₂ r₁ r₂ s₁ s₂ : ℝ)
    (hT : t₁ + t₂ ≠ 0) (z : Fin 3 → ℂ) :
    (dotProduct (star z) (q1SchurBlock t₁ t₂ r₁ r₂ s₁ s₂ *ᵥ z)).re =
      (t₁*t₂/(t₁+t₂)) * Complex.normSq ((r₁ : ℂ)*z 1 - (r₂ : ℂ)*z 0) +
      t₁ * Complex.normSq (z 0 + (r₁ : ℂ)*z 2) +
      t₂ * Complex.normSq (z 1 + (r₂ : ℂ)*z 2) +
      s₁ * Complex.normSq (z 1) + s₂ * Complex.normSq (z 0) +
      (s₁+s₂) * Complex.normSq (z 2) := by
  simp only [q1SchurBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.star_apply, Complex.star_def,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  field_simp [hT]
  ring

/-- For nonnegative `t₁` and `t₂` with positive sum and `s₁, s₂ ≥ 3`, the real quadratic form of
`q1SchurBlock` is at least three times the total squared coordinate norm. -/
theorem q1_schur_lower (t₁ t₂ r₁ r₂ s₁ s₂ : ℝ)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hT : 0 < t₁+t₂)
    (hs₁ : 3 ≤ s₁) (hs₂ : 3 ≤ s₂) (z : Fin 3 → ℂ) :
    3 * (∑ i, Complex.normSq (z i)) ≤
      (dotProduct (star z) (q1SchurBlock t₁ t₂ r₁ r₂ s₁ s₂ *ᵥ z)).re := by
  rw [q1_schur_quadratic_sos t₁ t₂ r₁ r₂ s₁ s₂ hT.ne' z]
  have ha := mul_nonneg (div_nonneg (mul_nonneg ht₁ ht₂) hT.le)
    (Complex.normSq_nonneg ((r₁ : ℂ)*z 1 - (r₂ : ℂ)*z 0))
  have hb := mul_nonneg ht₁ (Complex.normSq_nonneg (z 0 + (r₁ : ℂ)*z 2))
  have hc := mul_nonneg ht₂ (Complex.normSq_nonneg (z 1 + (r₂ : ℂ)*z 2))
  have h0 := Complex.normSq_nonneg (z 0)
  have h1 := Complex.normSq_nonneg (z 1)
  have h2 := Complex.normSq_nonneg (z 2)
  have hd := mul_le_mul_of_nonneg_right hs₁ h1
  have he := mul_le_mul_of_nonneg_right hs₂ h0
  have hf := mul_le_mul_of_nonneg_right (show 3 ≤ s₁+s₂ by linarith) h2
  rw [Fin.sum_univ_three]
  linarith

end Qatlib.Concepts.GramQueryCore.GramRealization.SchurTensorBlock
