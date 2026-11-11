/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceOneStepPropagator — Theorem 6 (block-encoded one-step propagator)

Fixed source: arXiv:2508.15170 (DissipDESolve25), Theorem 6, Equations (30)-(33),
page 13-14.

Statement (paper). Given the block-encoding `P_ℓ` of the one-step propagator
`Ξ_ℓ = T e^{∫_{ℓh}^{(ℓ+1)h} A(s) ds}`, one can construct a
`(α̃_ℓ, a1+1, ‖Ξ_ℓ‖ ε_a + ε0 + ε_a ε0)`-block-encoding `Pt_ℓ` satisfying
```
∏_{ℓ=0}^{M-1} α̃_ℓ = O( ∏_{ℓ=0}^{M-1} ‖Ξ_ℓ‖ ) ,          (30)
```
using `O(α_A T log(1/ε_a))` applications of (controlled)-`P_ℓ` and its inverse.

Formalization. The per-step construction is exactly Theorem 5 with `Ξ = Ξ_ℓ` and
`ε_ori = ε0` (that is how the paper obtains the error term via its Eq. (33)). The
product bound (30) is the arithmetic statement that with `δ = 1/M` the factor
`(1-δ)^M` is `Ω(1)`; we prove the explicit constant `(1-1/M)^M ≥ 1/9` for `M ≥ 2`
(from `(1-1/M)^M ≥ e^{-2}` and `e^2 < 9`), giving `∏α̃_ℓ ≤ 9 ∏‖Ξ_ℓ‖`.

The matrix-level product of `Pt_ℓ` across steps is the sequential application carried
out in the paper's Eq. (32); it is not re-derived in the present block-encoding
framework, which only provides the per-stage interface. The query count
`O(α_A T log(1/ε_a))` is the paper's cost bookkeeping; the per-step Theorem-5 cost is
already available as `theorem5_query_cost_comparison`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DissipDESolve25.MainResults.SourceOneStepPropagator

open Qatlib.Concepts.BlockEncoding

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Theorem 6, p.13-14: per-step construction. This is Theorem 5 with `Ξ = Ξ_ℓ` and
`ε_ori = ε0`, yielding the paper's per-step error `‖Ξ_ℓ‖ ε_a + ε0 + ε_a ε0`. -/
theorem theorem6_step_encoding
    {H I O H₂ : Type*} [Fintype H] [Fintype I] [Fintype O] [Fintype H₂]
    [DecidableEq H] [DecidableEq I] [DecidableEq O] [DecidableEq H₂]
    {Ξ : Matrix O I ℂ} {P : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε0 : ℝ} (hP : Qatlib.Concepts.BlockEncoding.BlockEncoding
      Ξ P L R α ε0)
    {Λ : Matrix O I ℂ} {Pt : Matrix H₂ H₂ ℂ} {L' : Matrix H₂ O ℂ} {R' : Matrix H₂ I ℂ}
    {αt ε_a : ℝ}
    (hamp : Qatlib.Concepts.BlockEncoding.BlockEncoding
      (Ξ + ε0 • Λ) Pt L' R' αt (ε_a * ‖Ξ + ε0 • Λ‖))
    (hΛ : ‖Λ‖ ≤ 1) (ha : 0 ≤ ε_a) :
    Qatlib.Concepts.BlockEncoding.BlockEncoding
      Ξ Pt L' R' αt (‖Ξ‖ * ε_a + ε0 + ε_a * ε0) := by
  have hε : 0 ≤ ε0 := hP.error_nonneg
  have hnorm : ‖Ξ + ε0 • Λ‖ ≤ ‖Ξ‖ + ε0 := by
    calc
      ‖Ξ + ε0 • Λ‖ ≤ ‖Ξ‖ + ‖ε0 • Λ‖ := norm_add_le _ _
      _ = ‖Ξ‖ + ε0 * ‖Λ‖ := by rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ‖Ξ‖ + ε0 := by
        have hmul : ε0 * ‖Λ‖ ≤ ε0 * 1 := mul_le_mul_of_nonneg_left hΛ hε
        nlinarith
  have hsub : ‖Ξ - (Ξ + ε0 • Λ)‖ ≤ ε0 := by
    have hneg : Ξ - (Ξ + ε0 • Λ) = -(ε0 • Λ) := by abel
    rw [hneg, norm_neg, norm_smul, Real.norm_of_nonneg hε]
    have hmul : ε0 * ‖Λ‖ ≤ ε0 * 1 := mul_le_mul_of_nonneg_left hΛ hε
    nlinarith
  have hstep : Qatlib.Concepts.BlockEncoding.BlockEncoding
      Ξ Pt L' R' αt (ε_a * ‖Ξ + ε0 • Λ‖ + ε0) :=
    hamp.perturb (by positivity) hsub
  have hfinal : ε_a * ‖Ξ + ε0 • Λ‖ + ε0 ≤ ‖Ξ‖ * ε_a + ε0 + ε_a * ε0 := by
    have hscaled : ε_a * ‖Ξ + ε0 • Λ‖ ≤ ε_a * (‖Ξ‖ + ε0) :=
      mul_le_mul_of_nonneg_left hnorm ha
    nlinarith [hscaled]
  exact hstep.mono hfinal

/-- Theorem 6, p.14: the paper chooses `δ = 1/M`; then the factor `(1-δ)^M` is
`Ω(1)`. We prove the explicit bound `(1-1/M)^M ≥ 1/9` for `M ≥ 2`. Proof route: the
exponent lower-bounds as `M log(1-1/M) ≥ -M/(M-1) ≥ -2`, and `e^{-2} ≥ 1/9`. -/
theorem one_sub_inv_pow_ge {M : ℕ} (hM : 2 ≤ M) :
    (1 / 9 : ℝ) ≤ (1 - 1 / (M : ℝ)) ^ M := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : (0 : ℕ) < M := lt_of_lt_of_le (by norm_num) hM
    exact_mod_cast this
  have hMge2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hbase_pos : 0 < 1 - 1 / (M : ℝ) := by
    rw [sub_pos, div_lt_one hMpos]
    have : (1 : ℕ) < M := by omega
    exact_mod_cast this
  -- Logarithmic lower bound: `M * log (1 - 1/M) ≥ -2`.
  have hlog_lower : -(2 : ℝ) ≤ (M : ℝ) * Real.log (1 - 1 / (M : ℝ)) := by
    have hM1pos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have hMposne : (M : ℝ) ≠ 0 := hMpos.ne'
    have hM1ne : ((M : ℝ) - 1) ≠ 0 := hM1pos.ne'
    have hlogeq : Real.log (1 - 1 / (M : ℝ)) = - Real.log ((M : ℝ) / ((M : ℝ) - 1)) := by
      rw [show 1 - 1 / (M : ℝ) = ((M : ℝ) - 1) / (M : ℝ) by field_simp]
      rw [Real.log_div hM1ne hMposne, Real.log_div hMposne hM1ne]
      ring
    have hlogle : Real.log ((M : ℝ) / ((M : ℝ) - 1)) ≤ 1 / ((M : ℝ) - 1) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (M : ℝ) / ((M : ℝ) - 1) by positivity)
      have hsub : (M : ℝ) / ((M : ℝ) - 1) - 1 = 1 / ((M : ℝ) - 1) := by field_simp; ring
      rwa [hsub] at h
    have hlog_ge : -(1 / ((M : ℝ) - 1)) ≤ Real.log (1 - 1 / (M : ℝ)) := by
      rw [hlogeq]; linarith
    have hmul_ge : (M : ℝ) * (-(1 / ((M : ℝ) - 1)))
        ≤ (M : ℝ) * Real.log (1 - 1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ge hMpos.le
    have hmul_eq : (M : ℝ) * (-(1 / ((M : ℝ) - 1))) = -((M : ℝ) / ((M : ℝ) - 1)) := by
      field_simp
    have hratio : (M : ℝ) / ((M : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hM1pos]
      linarith
    linarith [hmul_ge, hmul_eq, hratio]
  -- Exponentiate and identify with the power.
  have hexp_le : Real.exp (-(2 : ℝ))
      ≤ Real.exp ((M : ℝ) * Real.log (1 - 1 / (M : ℝ))) :=
    Real.exp_le_exp.mpr hlog_lower
  have hpow_eq : Real.exp ((M : ℝ) * Real.log (1 - 1 / (M : ℝ)))
      = (1 - 1 / (M : ℝ)) ^ M := by
    rw [← Real.log_pow (1 - 1 / (M : ℝ)) M,
      Real.exp_log (pow_pos hbase_pos M)]
  -- `e^{-2} ≥ 1/9`.
  have hexp2 : Real.exp (2 : ℝ) < 9 := by
    have h3 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
    have hsq : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hsq]
    nlinarith [h3, Real.exp_pos (1 : ℝ)]
  have h19 : (1 / 9 : ℝ) ≤ Real.exp (-(2 : ℝ)) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 2) (le_of_lt hexp2)
  calc
    (1 / 9 : ℝ) ≤ Real.exp (-(2 : ℝ)) := h19
    _ ≤ Real.exp ((M : ℝ) * Real.log (1 - 1 / (M : ℝ))) := hexp_le
    _ = (1 - 1 / (M : ℝ)) ^ M := hpow_eq

/-- Theorem 6, p.14, Equation (30): with `δ = 1/M`, `M ≥ 2`, and per-step factor bound
`α̃_ℓ ≤ ‖Ξ_ℓ‖/(1-δ)`, the product of the boosted factors is `O(∏‖Ξ_ℓ‖)`; concretely
`∏ α̃_ℓ ≤ 9 ∏ ‖Ξ_ℓ‖`. -/
theorem theorem6_product_factor
    {M : ℕ} (hM : 2 ≤ M) (Ξ αt : Fin M → ℝ)
    (hΞ : ∀ ℓ, 0 ≤ Ξ ℓ) (hα0 : ∀ ℓ, 0 ≤ αt ℓ)
    (hα : ∀ ℓ, αt ℓ ≤ Ξ ℓ / (1 - 1 / (M : ℝ))) :
    ∏ ℓ, αt ℓ ≤ 9 * ∏ ℓ, Ξ ℓ := by
  have hbase_pos : 0 < 1 - 1 / (M : ℝ) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : (0 : ℕ) < M := lt_of_lt_of_le (by norm_num) hM
      exact_mod_cast this
    rw [sub_pos, div_lt_one hMpos]
    have : (1 : ℕ) < M := by omega
    exact_mod_cast this
  have hden_pos : 0 < (1 - 1 / (M : ℝ)) ^ M := pow_pos hbase_pos M
  have hprod_le : ∏ ℓ, αt ℓ ≤ ∏ ℓ, (Ξ ℓ / (1 - 1 / (M : ℝ))) :=
    Finset.prod_le_prod₀ (fun ℓ _ => hα0 ℓ) (fun ℓ _ => hα ℓ)
  have hsplit : ∏ ℓ : Fin M, (Ξ ℓ / (1 - 1 / (M : ℝ)))
      = (∏ ℓ, Ξ ℓ) / (1 - 1 / (M : ℝ)) ^ M := by
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hP : 0 ≤ ∏ ℓ, Ξ ℓ := Finset.prod_nonneg (fun ℓ _ => hΞ ℓ)
  have hpow : (1 / 9 : ℝ) ≤ (1 - 1 / (M : ℝ)) ^ M := one_sub_inv_pow_ge hM
  have hquot : (∏ ℓ, Ξ ℓ) / (1 - 1 / (M : ℝ)) ^ M ≤ 9 * ∏ ℓ, Ξ ℓ := by
    rw [div_le_iff₀ hden_pos]
    have hmul : (9 * ∏ ℓ, Ξ ℓ) * (1 / 9) ≤ (9 * ∏ ℓ, Ξ ℓ) * (1 - 1 / (M : ℝ)) ^ M :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    nlinarith [hmul, hP]
  calc
    ∏ ℓ, αt ℓ ≤ ∏ ℓ, (Ξ ℓ / (1 - 1 / (M : ℝ))) := hprod_le
    _ = (∏ ℓ, Ξ ℓ) / (1 - 1 / (M : ℝ)) ^ M := hsplit
    _ ≤ 9 * ∏ ℓ, Ξ ℓ := hquot

/-- Theorem 6, p.14, assembled: given the per-step encodings with the Theorem-5 factor
bound `α̃_ℓ ≤ ‖Ξ_ℓ‖/(1-δ)`, the moment bound `‖Ξ_ℓ‖ ≥ 0`, and `δ = 1/M` with `M ≥ 2`,
the product of the boosted normalization factors obeys the paper's Eq. (30) with an
explicit constant `9`. -/
theorem theorem6_product_factor_bound
    {M : ℕ} (hM : 2 ≤ M) (Ξ αt : Fin M → ℝ)
    (hα0 : ∀ ℓ, 0 ≤ αt ℓ)
    (hbound : ∀ ℓ, αt ℓ ≤ ‖Ξ ℓ‖ / (1 - 1 / (M : ℝ))) :
    ∏ ℓ, αt ℓ ≤ 9 * ∏ ℓ, ‖Ξ ℓ‖ :=
  theorem6_product_factor hM (fun ℓ => ‖Ξ ℓ‖) αt (fun _ => norm_nonneg _)
    hα0 hbound

end Qatlib.Papers.DissipDESolve25.MainResults.SourceOneStepPropagator
