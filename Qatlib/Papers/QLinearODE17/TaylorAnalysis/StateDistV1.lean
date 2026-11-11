/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Lemmas 13-15 of `QLinearODE17`: normalization and postselection stability

Source: arXiv:1701.03684v2, Appendix B (printed Lemmas 13, 14 and 15).

* Lemma 13: normalizing two nearby vectors is `2β/α`-Lipschitz in the norm.
* Lemma 14: if the two-component states
  `α|0⟩|ψ₀⟩ + √(1-α²)|1⟩|ψ₁⟩` and `β|0⟩|φ₀⟩ + √(1-β²)|1⟩|φ₁⟩` are `δ`-close,
  then the postselected `|0⟩`-branches are `2δ/(α-δ)`-close.
* Lemma 15: under the same hypothesis the success amplitude `β` is at least
  `α - δ`.

The state difference is represented explicitly: the printed proofs only read the
`|0⟩`-component `‖α|ψ₀⟩ - β|φ₀⟩‖` of the joint `l²` norm. The joint-state
hypothesis below is the printed `‖|ψ⟩ - |φ⟩‖ ≤ δ` written out with that `l²`
norm, and `zero_component_le_of_sqrt_le` is exactly the step from the joint
bound to the component bound, so the branch results use no componentwise
shortcut. The printed `α, β ∈ [0,1]` bounds are not needed by the arguments
(`α, β ≥ 0` and unit branches suffice), so the statements below generalize them;
the `δ < α` side condition is only used by Lemma 14, where `α - δ` is the
denominator.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

/-- Printed Lemma 13: the normalized vector difference is at most `2β/α` when
`‖ψ‖ ≥ α > 0` and `‖ψ - φ‖ ≤ β`. -/
theorem normalized_sub_normalized_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α β : ℝ} {ψ φ : E} (hα : 0 < α) (hψ : α ≤ ‖ψ‖) (hδ : ‖ψ - φ‖ ≤ β) :
    ‖(‖ψ‖⁻¹ : ℝ) • ψ - (‖φ‖⁻¹ : ℝ) • φ‖ ≤ 2 * β / α := by
  have hψpos : 0 < ‖ψ‖ := lt_of_lt_of_le hα hψ
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hδ
  rcases eq_or_lt_of_le (norm_nonneg φ) with hφ0 | hφpos
  · have hφz : φ = 0 := norm_eq_zero.mp hφ0.symm
    subst hφz
    have hlt : ‖ψ‖ ≤ β := by simpa using hδ
    have hL : ‖(‖ψ‖⁻¹ : ℝ) • ψ - (‖(0 : E)‖⁻¹ : ℝ) • (0 : E)‖ = 1 := by
      simp only [norm_zero, inv_zero, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hψpos, inv_mul_cancel₀ hψpos.ne']
    rw [hL, le_div_iff₀ hα]
    linarith
  · have hdecomp : (‖ψ‖⁻¹ : ℝ) • ψ - (‖φ‖⁻¹ : ℝ) • φ =
        (‖ψ‖⁻¹ : ℝ) • (ψ - φ) + ((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ := by
      rw [smul_sub, sub_smul]
      abel
    rw [hdecomp]
    have h1 : ‖(‖ψ‖⁻¹ : ℝ) • (ψ - φ)‖ = ‖ψ‖⁻¹ * ‖ψ - φ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hψpos]
    have h2 : ‖((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ‖ = |‖φ‖ - ‖ψ‖| / ‖ψ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have hinv : |(‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)| * ‖φ‖ = |‖φ‖ - ‖ψ‖| / ‖ψ‖ := by
        have h : (‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ) = (‖φ‖ - ‖ψ‖) / (‖ψ‖ * ‖φ‖) := by
          field_simp
        rw [h, abs_div, abs_mul, abs_of_pos hψpos, abs_of_pos hφpos, div_mul_eq_mul_div,
          mul_div_mul_right _ _ hφpos.ne']
      rw [hinv]
    calc ‖(‖ψ‖⁻¹ : ℝ) • (ψ - φ) + ((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ‖
        ≤ ‖(‖ψ‖⁻¹ : ℝ) • (ψ - φ)‖ + ‖((‖ψ‖⁻¹ : ℝ) - (‖φ‖⁻¹ : ℝ)) • φ‖ := norm_add_le _ _
      _ = ‖ψ‖⁻¹ * ‖ψ - φ‖ + |‖φ‖ - ‖ψ‖| / ‖ψ‖ := by rw [h1, h2]
      _ ≤ 2 * β / α := by
          have habs : |‖φ‖ - ‖ψ‖| ≤ β := by
            rw [abs_sub_comm]
            exact (abs_norm_sub_norm_le ψ φ).trans hδ
          have hsum : ‖ψ‖⁻¹ * ‖ψ - φ‖ + |‖φ‖ - ‖ψ‖| / ‖ψ‖ ≤
              ‖ψ‖⁻¹ * β + β / ‖ψ‖ := by
            have h3 : |‖φ‖ - ‖ψ‖| / ‖ψ‖ ≤ β / ‖ψ‖ :=
              div_le_div_of_nonneg_right habs hψpos.le
            have h4 : ‖ψ‖⁻¹ * ‖ψ - φ‖ ≤ ‖ψ‖⁻¹ * β :=
              mul_le_mul_of_nonneg_left hδ (inv_nonneg.mpr hψpos.le)
            linarith
          have heq : ‖ψ‖⁻¹ * β + β / ‖ψ‖ = 2 * β / ‖ψ‖ := by
            field_simp
            ring
          rw [heq] at hsum
          have hfin : 2 * β / ‖ψ‖ ≤ 2 * β / α := by
            rw [div_le_div_iff₀ hψpos hα]
            have hmul : 2 * β * α ≤ 2 * β * ‖ψ‖ :=
              mul_le_mul_of_nonneg_left hψ (by linarith)
            linarith
          linarith

/-- Reading the `|0⟩`-component bound off the joint `l²` state norm: if
`√(‖u‖² + ‖w‖²) ≤ δ` then `‖u‖ ≤ δ`. -/
theorem zero_component_le_of_sqrt_le {E : Type*} [NormedAddCommGroup E]
    {u w : E} {δ : ℝ} (h : Real.sqrt (‖u‖ ^ 2 + ‖w‖ ^ 2) ≤ δ) : ‖u‖ ≤ δ := by
  have h1 : ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
  have h2 : Real.sqrt (‖u‖ ^ 2) ≤ Real.sqrt (‖u‖ ^ 2 + ‖w‖ ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  linarith

/-- Printed Lemma 14: two `δ`-close two-component states have `|0⟩`-branches at
distance at most `2δ/(α-δ)`. -/
theorem lemma14_state_zero_component {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α β δ : ℝ} {ψ₀ ψ₁ φ₀ φ₁ : E}
    (hψ₀ : ‖ψ₀‖ = 1) (hφ₀ : ‖φ₀‖ = 1) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hstate : Real.sqrt (‖α • ψ₀ - β • φ₀‖ ^ 2 +
      ‖Real.sqrt (1 - α ^ 2) • ψ₁ - Real.sqrt (1 - β ^ 2) • φ₁‖ ^ 2) ≤ δ)
    (hδα : δ < α) :
    ‖φ₀ - ψ₀‖ ≤ 2 * δ / (α - δ) := by
  have hzero : ‖α • ψ₀ - β • φ₀‖ ≤ δ := zero_component_le_of_sqrt_le hstate
  have hαpos : 0 < α := lt_of_le_of_lt (le_trans (norm_nonneg _) hzero) hδα
  have hnα : ‖α • ψ₀‖ = α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0, hψ₀, mul_one]
  have hnb : ‖β • φ₀‖ = β := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0, hφ₀, mul_one]
  have hβpos : 0 < β := by
    have htri : ‖α • ψ₀‖ - ‖β • φ₀‖ ≤ ‖α • ψ₀ - β • φ₀‖ := norm_sub_norm_le _ _
    rw [hnα, hnb] at htri
    linarith
  have hmain := normalized_sub_normalized_le hαpos (le_of_eq hnα.symm) hzero
  have hleft : (‖α • ψ₀‖⁻¹ : ℝ) • (α • ψ₀) = ψ₀ := by
    rw [hnα]
    exact inv_smul_smul₀ hαpos.ne' ψ₀
  have hright : (‖β • φ₀‖⁻¹ : ℝ) • (β • φ₀) = φ₀ := by
    rw [hnb]
    exact inv_smul_smul₀ hβpos.ne' φ₀
  rw [hleft, hright] at hmain
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hzero
  have hfinal : 2 * δ / α ≤ 2 * δ / (α - δ) := by
    rw [div_le_div_iff₀ hαpos (by linarith : 0 < α - δ)]
    have hmul : 2 * δ * (α - δ) ≤ 2 * δ * α :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  rw [norm_sub_rev]
  linarith

/-- Printed Lemma 15: two `δ`-close two-component states have success amplitude
`β ≥ α - δ`. -/
theorem lemma15_state_zero_component_prob_ge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {α β δ : ℝ} {ψ₀ ψ₁ φ₀ φ₁ : E}
    (hψ₀ : ‖ψ₀‖ = 1) (hφ₀ : ‖φ₀‖ = 1) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hstate : Real.sqrt (‖α • ψ₀ - β • φ₀‖ ^ 2 +
      ‖Real.sqrt (1 - α ^ 2) • ψ₁ - Real.sqrt (1 - β ^ 2) • φ₁‖ ^ 2) ≤ δ) :
    α - δ ≤ β := by
  have hzero : ‖α • ψ₀ - β • φ₀‖ ≤ δ := zero_component_le_of_sqrt_le hstate
  have hnα : ‖α • ψ₀‖ = α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0, hψ₀, mul_one]
  have hnb : ‖β • φ₀‖ = β := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0, hφ₀, mul_one]
  have htri : ‖α • ψ₀‖ - ‖β • φ₀‖ ≤ ‖α • ψ₀ - β • φ₀‖ := norm_sub_norm_le _ _
  rw [hnα, hnb] at htri
  linarith

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
