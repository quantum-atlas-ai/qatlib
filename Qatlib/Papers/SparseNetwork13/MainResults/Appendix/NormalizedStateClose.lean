/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — Lemma A.1: nearby states have nearby normalisations

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

Lemma A.1 (Appendix A, p.37).  Let `|ψ⟩` and `|φ⟩` be two unnormalised states with
`‖|ψ⟩‖ ≥ α > 0` and `‖|ψ⟩ − |φ⟩‖ ≤ β`.  Then

  `‖ |ψ⟩/‖|ψ⟩‖ − |φ⟩/‖|φ⟩‖ ‖ ≤ 2β/α`.   (A.1)

Proof (p.37, Eq. (A.2)--(A.7)): split
`ψ̂ − φ̂ = (ψ̂ − φ/‖ψ‖) + (φ/‖ψ‖ − φ̂)`, apply the triangle inequality,
bound `‖ψ̂ − φ/‖ψ‖‖ = ‖ψ − φ‖/‖ψ‖ ≤ β/α`, and bound the second term by
`‖φ‖·|1/‖ψ‖ − 1/‖φ‖| = |‖ψ‖ − ‖φ‖|/‖ψ‖ ≤ β/α`.  Summing gives `2β/α`.

The paper writes the normalised vector as `|ψ⟩/‖|ψ⟩‖`; in a real normed space this is
the scalar multiple `(‖ψ‖)⁻¹ • |ψ⟩`.  The paper tacitly assumes `‖|φ⟩‖ ≠ 0` (otherwise
`|φ⟩/‖|φ⟩‖` is undefined); here we cover that degenerate case explicitly rather than
impose it as an extra hypothesis, so the statement holds for *all* `|φ⟩`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Appendix

/-- Scalar arithmetic behind Eq. (A.5): for `a, b > 0`,
`|a⁻¹ − b⁻¹| · b = |b − a| / a`.  (The paper writes `‖φ‖ |1/‖ψ‖ − 1/‖φ‖|` as
`|‖ψ‖ − ‖φ‖| / ‖ψ‖`.) -/
theorem abs_inv_sub_inv_mul_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| * b = |b - a| / a := by
  have hab : 0 < a * b := mul_pos ha hb
  have hkey : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos hab]
  field_simp

/-- **Lemma A.1 (arXiv:1311.1851v10, Appendix A, p.37).**  If `α > 0`, `α ≤ ‖ψ‖`,
and `‖ψ − φ‖ ≤ β`, then the normalised states are within `2β/α`:
`‖(‖ψ‖)⁻¹ • ψ − (‖φ‖)⁻¹ • φ‖ ≤ 2β/α`.  This is Eq. (A.1), with `|ψ⟩/‖|ψ⟩‖`
written as the scalar multiple `(‖ψ‖)⁻¹ • |ψ⟩`. -/
theorem lemmaA1_normalized_state_close {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (x y : W) {α β : ℝ} (hα : 0 < α) (hx : α ≤ ‖x‖) (hxy : ‖x - y‖ ≤ β) :
    ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤ 2 * β / α := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hα hx
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg (x - y)) hxy
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
  · -- Degenerate case `‖φ‖ = 0`: then `φ = 0` and the normalised `φ` term vanishes.
    have hy : y = 0 := norm_eq_zero.mp hy0.symm
    subst hy
    have hnorm : ‖(‖x‖)⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hxpos,
        inv_mul_cancel₀ (ne_of_gt hxpos)]
    simp only [smul_zero, sub_zero]
    rw [hnorm]
    -- `1 ≤ 2β/α`, since `α ≤ β`.
    have hβ : α ≤ β := le_trans hx (by simpa using hxy)
    rw [le_div_iff₀ hα]
    nlinarith
  · -- Main case `‖φ‖ > 0`.  Split as in Eq. (A.2).
    have hdecomp : (‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y
        = (‖x‖)⁻¹ • (x - y) + ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y := by
      rw [smul_sub, sub_smul]
      abel
    rw [hdecomp]
    have htri := norm_add_le ((‖x‖)⁻¹ • (x - y)) (((‖x‖)⁻¹ - (‖y‖)⁻¹) • y)
    have h1 : ‖(‖x‖)⁻¹ • (x - y)‖ = (‖x‖)⁻¹ * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hxpos))]
    have h2 : ‖((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖ = |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [h1, h2] at htri
    -- First term, Eq. (A.4): `‖ψ − φ‖/‖ψ‖ ≤ β/α`.
    have hA : (‖x‖)⁻¹ * ‖x - y‖ ≤ β / α := by
      have hinv : (‖x‖)⁻¹ ≤ α⁻¹ := (inv_le_inv₀ hxpos hα).mpr hx
      calc (‖x‖)⁻¹ * ‖x - y‖ ≤ α⁻¹ * β :=
              mul_le_mul hinv hxy (norm_nonneg _) (le_of_lt (inv_pos.mpr hα))
        _ = β / α := by rw [div_eq_mul_inv]; ring
    -- Second term, Eq. (A.5)--(A.6): `|‖ψ‖ − ‖φ‖|/‖ψ‖ ≤ β/α`.
    have hB : |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ ≤ β / α := by
      rw [abs_inv_sub_inv_mul_eq hxpos hypos]
      have hstep : |‖y‖ - ‖x‖| ≤ β := by
        have h := abs_norm_sub_norm_le y x
        rw [norm_sub_rev] at h
        exact le_trans h hxy
      have e1 : |‖y‖ - ‖x‖| / ‖x‖ ≤ β / ‖x‖ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hxpos))
      have hinv : (‖x‖)⁻¹ ≤ α⁻¹ := (inv_le_inv₀ hxpos hα).mpr hx
      have e2 : β / ‖x‖ ≤ β / α := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv hβ0
      exact le_trans e1 e2
    calc ‖(‖x‖)⁻¹ • (x - y) + ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖
        ≤ (‖x‖)⁻¹ * ‖x - y‖ + |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ := htri
      _ ≤ β / α + β / α := add_le_add hA hB
      _ = 2 * β / α := by ring

end Qatlib.Papers.SparseNetwork13.MainResults.Appendix
