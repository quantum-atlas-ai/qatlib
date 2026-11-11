/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Method of lines for parabolic PDEs — Lemma 25 of arXiv:2606.03407v1

Fixed version: arXiv:2606.03407v1 (submitted 2026-06-02), PDF p.64,
Appendix D, Lemma 25.

The paper's final readout step normalises two vectors and compares the
normalised states.  Lemma 25 controls that comparison by the relative error
`2 ‖ψ − φ‖₂ / ‖ψ‖₂`: the triangle inequality splits the difference into a
term along `ψ` and a term along `φ`, and the second term is bounded by the
reverse triangle inequality `|‖ψ‖ − ‖φ‖| ≤ ‖ψ − φ‖`.

The statement is formalised over a real normed space, which is the setting of
the norm-only estimate; the same estimate holds verbatim for complex vectors
because only `‖·‖` is used, so no positivity of an inner product is required.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open scoped Real

/-- The normalised unit vector `ψ / ‖ψ‖₂`, written with an explicit real scalar
inverse so that it lives in a general real normed space. -/
noncomputable def unitVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E) : E :=
  (‖ψ‖⁻¹ : ℝ) • ψ

/-- `unitVector` has norm one for a non-zero vector. -/
theorem norm_unitVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E) (hψ : ψ ≠ 0) : ‖unitVector ψ‖ = 1 := by
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  rw [unitVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- Fixed arXiv:2606.03407v1, Appendix D, Lemma 25 (PDF p.64):
for two non-zero vectors `ψ`, `φ`,

`‖ψ/‖ψ‖₂ − φ/‖φ‖₂‖₂ ≤ 2 ‖ψ − φ‖₂ / ‖ψ‖₂`.

This is the paper's exact estimate; the proof is the paper's proof
(triangle inequality + reverse triangle inequality). -/
theorem norm_unitVector_sub_unitVector_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ φ : E) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    ‖unitVector ψ - unitVector φ‖ ≤ 2 * ‖ψ - φ‖ / ‖ψ‖ := by
  have hψpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hφpos : 0 < ‖φ‖ := norm_pos_iff.mpr hφ
  -- Step 1: split through the common midpoint `‖ψ‖⁻¹ • φ`.
  have hsplit :
      ‖unitVector ψ - unitVector φ‖
        ≤ ‖(‖ψ‖⁻¹ : ℝ) • (ψ - φ)‖
          + ‖((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ‖ := by
    have htri := norm_add_le
      ((‖ψ‖⁻¹ : ℝ) • ψ - (‖ψ‖⁻¹ : ℝ) • φ)
      ((‖ψ‖⁻¹ : ℝ) • φ - (‖φ‖⁻¹ : ℝ) • φ)
    have hsum :
        ((‖ψ‖⁻¹ : ℝ) • ψ - (‖ψ‖⁻¹ : ℝ) • φ)
          + ((‖ψ‖⁻¹ : ℝ) • φ - (‖φ‖⁻¹ : ℝ) • φ)
          = unitVector ψ - unitVector φ := by
      rw [unitVector]
      abel
    have hfirst :
        (‖ψ‖⁻¹ : ℝ) • ψ - (‖ψ‖⁻¹ : ℝ) • φ
          = (‖ψ‖⁻¹ : ℝ) • (ψ - φ) := by
      rw [smul_sub]
    have hsecond :
        (‖ψ‖⁻¹ : ℝ) • φ - (‖φ‖⁻¹ : ℝ) • φ
          = ((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ := by
      rw [sub_smul]
    rw [hsum, hfirst, hsecond] at htri
    exact htri
  -- Step 2: evaluate the two norms.
  have hfirst : ‖(‖ψ‖⁻¹ : ℝ) • (ψ - φ)‖ = ‖ψ - φ‖ / ‖ψ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hψpos]
    field_simp
  have hsecond :
      ‖((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ‖ ≤ ‖ψ - φ‖ / ‖ψ‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hdiff : (‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ) = (‖φ‖ - ‖ψ‖) / (‖ψ‖ * ‖φ‖) :=
      inv_sub_inv hψpos.ne' hφpos.ne'
    rw [hdiff, abs_div, abs_mul, abs_of_pos hψpos, abs_of_pos hφpos,
      div_mul_eq_mul_div, mul_div_mul_right _ _ hφpos.ne']
    have hrev : |‖φ‖ - ‖ψ‖| ≤ ‖ψ - φ‖ := by
      have h := abs_norm_sub_norm_le φ ψ
      rw [norm_sub_rev] at h
      exact h
    exact div_le_div_of_nonneg_right hrev (le_of_lt hψpos)
  -- Step 3: combine.
  calc ‖unitVector ψ - unitVector φ‖
      ≤ ‖ψ - φ‖ / ‖ψ‖ + ‖ψ - φ‖ / ‖ψ‖ := by linarith [hsplit, hfirst, hsecond]
    _ = 2 * ‖ψ - φ‖ / ‖ψ‖ := by ring

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
