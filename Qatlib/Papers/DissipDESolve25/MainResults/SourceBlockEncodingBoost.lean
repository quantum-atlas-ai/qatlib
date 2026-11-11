/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceBlockEncodingBoost — Theorem 5 (block-encoding factor boost)

Fixed source: arXiv:2508.15170 (DissipDESolve25), Theorem 5, Equations (27)-(28), page 13.

Statement (paper). Let `U` be an `(α, m, ε_ori)`-block-encoding of `Ξ`. Then one can
construct an `(α', m+1, ε_a ‖Ξ‖ + ε_ori + ε_a ε_ori)`-block-encoding `Ũ` of `Ξ` such
that `α' ≤ ‖Ξ‖/(1-δ)`, using `O(α / (δ‖Ξ‖) * log(α / (‖Ξ‖ ε_a)))` applications of
(controlled)-`U` and its inverse.

Formalization plan, following the paper's proof verbatim:

* `exists_perturbed_exact_encoding` — the paper's opening sentence "Consider `U` as a
  `(α, m, 0)`-block-encoding of `Ξ + ε_ori Λ` where `‖Λ‖ ≤ 1`". Provable from the input
  `BlockEncoding Ξ U L R α ε_ori` by taking `Λ` to be the (scaled) compression residual.
* `boost_factor_bound` — Equation (28): `‖Ξ + ε_ori Λ‖/(1-δ/2) ≤ ‖Ξ‖/(1-δ)`.
* `boost_error_bound` — the accumulated error `ε_a‖Ξ+ε_oriΛ‖ + ε_ori ≤ ε_a‖Ξ‖ + ε_ori + ε_a ε_ori`.
* `theorem5_query_cost_comparison` — Equation (27): the amplification cost measured
  against `Ξ + ε_ori Λ` is dominated by the cost measured against `Ξ`.
* `theorem5_block_encoding` — the assembled conclusion: a `BlockEncoding Ξ Ũ L' R' β`
  with `β ≤ ‖Ξ‖/(1-δ)` and error `ε_a‖Ξ‖ + ε_ori + ε_a ε_ori`.

The uniform singular value amplification subroutine itself (their citation `[17,31]`,
Liu--Su 2024 / Gilyén et al. 2019) is not re-derived here; it enters as the explicit
hypothesis `hamp` (the made `(α', m+1, ε_a‖Ξ+ε_oriΛ‖)` block-encoding of `Ξ+ε_oriΛ`).
All parameter arithmetic around it is proved.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

namespace Qatlib.Papers.DissipDESolve25.MainResults.SourceBlockEncodingBoost

open Qatlib.Concepts.BlockEncoding

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- Theorem 5, p.13, first step: an `(α, ε_ori)` block-encoding of `Ξ` is an exact
`(α, 0)` block-encoding of a perturbed operator `Ξ + ε_ori • Λ` with `‖Λ‖ ≤ 1`.
This is the paper's "Consider `U` as a `(α, m, 0)`-block-encoding of `Ξ + ε_ori Λ`
where `‖Λ‖ ≤ 1`". -/
theorem exists_perturbed_exact_encoding
    {Ξ : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε_ori : ℝ} (h : BlockEncoding Ξ U L R α ε_ori) :
    ∃ Λ : Matrix O I ℂ, ‖Λ‖ ≤ 1 ∧ BlockEncoding (Ξ + ε_ori • Λ) U L R α 0 := by
  by_cases hε : ε_ori = 0
  · -- Degenerate case: the input error already vanishes, so `Λ = 0` works.
    have hzero : ‖Ξ - α • compress L U R‖ ≤ 0 := by simpa [hε] using h.error_le
    have hB : Ξ = α • compress L U R := by
      have hsub : Ξ - α • compress L U R = 0 := norm_le_zero_iff.mp hzero
      exact sub_eq_zero.mp hsub
    refine ⟨0, by simp, h.unitary, h.left_isometry, h.right_isometry,
      h.normalization_pos, le_rfl, ?_⟩
    simp [hB]
  · -- Genuine case: `Λ = ε_ori⁻¹ • (α • compress L U R - Ξ)`.
    have hεpos : 0 < ε_ori := lt_of_le_of_ne h.error_nonneg (Ne.symm hε)
    have hle : ‖α • compress L U R - Ξ‖ ≤ ε_ori := by
      simpa [norm_sub_rev] using h.error_le
    refine ⟨ε_ori⁻¹ • (α • compress L U R - Ξ), ?_, h.unitary, h.left_isometry,
      h.right_isometry, h.normalization_pos, le_rfl, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc
        ε_ori⁻¹ * ‖α • compress L U R - Ξ‖ ≤ ε_ori⁻¹ * ε_ori :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 1 := by field_simp
    · have hcancel :
          ε_ori • (ε_ori⁻¹ • (α • compress L U R - Ξ)) = (α • compress L U R - Ξ) := by
        rw [smul_smul, mul_inv_cancel₀ hε, one_smul]
      rw [hcancel]
      have hsum : Ξ + (α • compress L U R - Ξ) = α • compress L U R := by abel
      rw [hsum]
      simp

omit [DecidableEq O] in
/-- Theorem 5, p.13, Equation (28): under the smallness condition
`ε_ori ≤ ‖Ξ‖ · (δ/2)/(1-δ)`, the boosted normalization factor obeys
`‖Ξ + ε_ori • Λ‖/(1-δ/2) ≤ ‖Ξ‖/(1-δ)`, given `‖Λ‖ ≤ 1`. -/
theorem boost_factor_bound
    {Ξ Λ : Matrix O I ℂ} {δ ε_ori : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΛ : ‖Λ‖ ≤ 1) (hε : 0 ≤ ε_ori)
    (hsmall : ε_ori ≤ ‖Ξ‖ * (δ / 2) / (1 - δ)) :
    ‖Ξ + ε_ori • Λ‖ / (1 - δ / 2) ≤ ‖Ξ‖ / (1 - δ) := by
  have hden1 : 0 < 1 - δ / 2 := by nlinarith
  have hden2 : 0 < 1 - δ := by nlinarith
  have hnorm : ‖Ξ + ε_ori • Λ‖ ≤ ‖Ξ‖ + ε_ori := by
    calc
      ‖Ξ + ε_ori • Λ‖ ≤ ‖Ξ‖ + ‖ε_ori • Λ‖ := norm_add_le _ _
      _ = ‖Ξ‖ + ε_ori * ‖Λ‖ := by rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ‖Ξ‖ + ε_ori := by
        have hmul : ε_ori * ‖Λ‖ ≤ ε_ori * 1 := mul_le_mul_of_nonneg_left hΛ hε
        nlinarith
  have harith : (‖Ξ‖ + ε_ori) / (1 - δ / 2) ≤ ‖Ξ‖ / (1 - δ) := by
    rw [div_le_div_iff₀ hden1 hden2]
    have hcut : ε_ori * (1 - δ) ≤ ‖Ξ‖ * (δ / 2) := by
      rw [le_div_iff₀ hden2] at hsmall
      linarith
    nlinarith [hcut]
  calc
    ‖Ξ + ε_ori • Λ‖ / (1 - δ / 2) ≤ (‖Ξ‖ + ε_ori) / (1 - δ / 2) := by gcongr
    _ ≤ ‖Ξ‖ / (1 - δ) := harith

omit [DecidableEq O] in
/-- Theorem 5, p.13: error accumulation. With `‖Λ‖ ≤ 1`, `0 ≤ ε_ori`, `0 ≤ ε_a`, the
error `ε_a ‖Ξ + ε_ori • Λ‖ + ε_ori` is bounded by the paper's claimed
`ε_a ‖Ξ‖ + ε_ori + ε_a ε_ori`. -/
theorem boost_error_bound
    {Ξ Λ : Matrix O I ℂ} {ε_ori ε_a : ℝ}
    (hε : 0 ≤ ε_ori) (ha : 0 ≤ ε_a) (hΛ : ‖Λ‖ ≤ 1) :
    ε_a * ‖Ξ + ε_ori • Λ‖ + ε_ori ≤ ε_a * ‖Ξ‖ + ε_ori + ε_a * ε_ori := by
  have hnorm : ‖Ξ + ε_ori • Λ‖ ≤ ‖Ξ‖ + ε_ori := by
    calc
      ‖Ξ + ε_ori • Λ‖ ≤ ‖Ξ‖ + ‖ε_ori • Λ‖ := norm_add_le _ _
      _ = ‖Ξ‖ + ε_ori * ‖Λ‖ := by rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ‖Ξ‖ + ε_ori := by
        have hmul : ε_ori * ‖Λ‖ ≤ ε_ori * 1 := mul_le_mul_of_nonneg_left hΛ hε
        nlinarith
  have hscaled : ε_a * ‖Ξ + ε_ori • Λ‖ ≤ ε_a * (‖Ξ‖ + ε_ori) :=
    mul_le_mul_of_nonneg_left hnorm ha
  nlinarith [hscaled]

omit [DecidableEq O] in
/-- Theorem 5, p.13, Equation (27): the amplification cost measured with the perturbed
factor `‖Ξ + ε_ori • Λ‖` is dominated by the same expression measured with `‖Ξ‖`, in the
regime `‖Ξ‖ ≤ ‖Ξ + ε_ori • Λ‖` and `α/(ε_a ‖Ξ + ε_ori • Λ‖) ≥ 1` where that comparison
is literal (the paper absorbs the difference in the big-`O`). -/
theorem theorem5_query_cost_comparison
    {Ξ Λ : Matrix O I ℂ} {α δ ε_ori ε_a : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (ha : 0 < ε_a)
    (hΞ : 0 < ‖Ξ‖)
    (hmono : ‖Ξ‖ ≤ ‖Ξ + ε_ori • Λ‖)
    (hlog1 : 1 ≤ α / (ε_a * ‖Ξ + ε_ori • Λ‖)) :
    (α / (δ * ‖Ξ + ε_ori • Λ‖)) * Real.log (α / (ε_a * ‖Ξ + ε_ori • Λ‖))
      ≤ (α / (δ * ‖Ξ‖)) * Real.log (α / (ε_a * ‖Ξ‖)) := by
  have hΞp : 0 < ‖Ξ + ε_ori • Λ‖ := lt_of_lt_of_le hΞ hmono
  have hdenp : 0 < δ * ‖Ξ + ε_ori • Λ‖ := mul_pos hδ hΞp
  have hden : 0 < δ * ‖Ξ‖ := mul_pos hδ hΞ
  have hterm1 : α / (δ * ‖Ξ + ε_ori • Λ‖) ≤ α / (δ * ‖Ξ‖) := by
    rw [div_le_div_iff₀ hdenp hden]
    have h : δ * ‖Ξ‖ ≤ δ * ‖Ξ + ε_ori • Λ‖ := mul_le_mul_of_nonneg_left hmono hδ.le
    nlinarith [h, hα.le]
  have harg : α / (ε_a * ‖Ξ + ε_ori • Λ‖) ≤ α / (ε_a * ‖Ξ‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : ε_a * ‖Ξ‖ ≤ ε_a * ‖Ξ + ε_ori • Λ‖ := mul_le_mul_of_nonneg_left hmono ha.le
    nlinarith [h, hα.le]
  have hlog_le : Real.log (α / (ε_a * ‖Ξ + ε_ori • Λ‖))
      ≤ Real.log (α / (ε_a * ‖Ξ‖)) :=
    Real.log_le_log (by positivity) harg
  have hlog_src_nonneg : 0 ≤ Real.log (α / (ε_a * ‖Ξ + ε_ori • Λ‖)) :=
    Real.log_nonneg hlog1
  have hb_nonneg : 0 ≤ α / (δ * ‖Ξ‖) := by positivity
  exact mul_le_mul hterm1 hlog_le hlog_src_nonneg hb_nonneg

/-- Theorem 5, p.13, assembled: given the input `(α, ε_ori)`-block-encoding `U` of `Ξ`
and the amplification subroutine output `Ũ` that is a `(β, ε_a‖Ξ + ε_ori • Λ‖)`-block-
encoding of `Ξ + ε_ori • Λ` (the `[17,31]` amplification, supplied here as `hamp`),
the composite is a `(β, ε_a‖Ξ‖ + ε_ori + ε_a ε_ori)`-block-encoding of `Ξ`, and
`β = α' ≤ ‖Ξ‖/(1-δ)` whenever the subroutine's factor does. -/
theorem theorem5_block_encoding
    {Ξ : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε_ori : ℝ} (hU : BlockEncoding Ξ U L R α ε_ori)
    {Λ : Matrix O I ℂ}
    {H₂ : Type*} [Fintype H₂] [DecidableEq H₂]
    {Ũ : Matrix H₂ H₂ ℂ} {L' : Matrix H₂ O ℂ} {R' : Matrix H₂ I ℂ}
    {β ε_a : ℝ}
    (hamp : BlockEncoding (Ξ + ε_ori • Λ) Ũ L' R' β (ε_a * ‖Ξ + ε_ori • Λ‖))
    (hΛ : ‖Λ‖ ≤ 1) (ha : 0 ≤ ε_a) :
    BlockEncoding Ξ Ũ L' R' β (ε_a * ‖Ξ‖ + ε_ori + ε_a * ε_ori) := by
  have hε : 0 ≤ ε_ori := hU.error_nonneg
  have hnorm : ‖Ξ - (Ξ + ε_ori • Λ)‖ ≤ ε_ori := by
    have hsub : Ξ - (Ξ + ε_ori • Λ) = -(ε_ori • Λ) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_of_nonneg hε]
    have hmul : ε_ori * ‖Λ‖ ≤ ε_ori * 1 := mul_le_mul_of_nonneg_left hΛ hε
    nlinarith
  have hstep : BlockEncoding Ξ Ũ L' R' β (ε_a * ‖Ξ + ε_ori • Λ‖ + ε_ori) :=
    hamp.perturb (by positivity) hnorm
  have hfinal : ε_a * ‖Ξ + ε_ori • Λ‖ + ε_ori ≤ ε_a * ‖Ξ‖ + ε_ori + ε_a * ε_ori :=
    boost_error_bound hε ha hΛ
  exact hstep.mono hfinal

/-- Theorem 5, p.13, full conclusion: combining the assembled block encoding with the
factor bound (28), the boosted factor satisfies `β ≤ ‖Ξ‖/(1-δ)` and the result is the
paper's `(α', m+1, ε_a‖Ξ‖ + ε_ori + ε_a ε_ori)`-block-encoding of `Ξ`. -/
theorem theorem5_full
    {Ξ : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε_ori : ℝ} (hU : BlockEncoding Ξ U L R α ε_ori)
    {Λ : Matrix O I ℂ}
    {H₂ : Type*} [Fintype H₂] [DecidableEq H₂]
    {Ũ : Matrix H₂ H₂ ℂ} {L' : Matrix H₂ O ℂ} {R' : Matrix H₂ I ℂ}
    {β ε_a δ : ℝ}
    (hamp : BlockEncoding (Ξ + ε_ori • Λ) Ũ L' R' β (ε_a * ‖Ξ + ε_ori • Λ‖))
    (hΛ : ‖Λ‖ ≤ 1) (ha : 0 ≤ ε_a)
    (hβ : β ≤ ‖Ξ + ε_ori • Λ‖ / (1 - δ / 2))
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : ε_ori ≤ ‖Ξ‖ * (δ / 2) / (1 - δ)) :
    BlockEncoding Ξ Ũ L' R' β (ε_a * ‖Ξ‖ + ε_ori + ε_a * ε_ori) ∧
      β ≤ ‖Ξ‖ / (1 - δ) := by
  refine ⟨theorem5_block_encoding hU hamp hΛ ha, ?_⟩
  exact hβ.trans (boost_factor_bound hδ hδ1 hΛ hU.error_nonneg hsmall)

end Qatlib.Papers.DissipDESolve25.MainResults.SourceBlockEncodingBoost
