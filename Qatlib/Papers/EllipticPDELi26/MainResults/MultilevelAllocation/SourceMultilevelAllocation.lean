/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# SourceMultilevelAllocation — Lemma 4.1 of arXiv:2606.01270v2

Xiantao Li, arXiv:2606.01270v2 (2026-09-22).  Section 4, Lemma 4.1, pages 10–11.

For a multilevel decomposition `Q_L = ∑_{ℓ=0}^{L} Δ_ℓ` (4.1) the level-wise cost model of
Lemma 4.1 is:

* Amplitude-estimation branch: level `ℓ` estimates `Δ_ℓ` to additive accuracy `ε_ℓ` at cost
  `Õ(c_ℓ / ε_ℓ)`; the total budget is `∑_ℓ ε_ℓ ≤ ε`.  The optimized total cost is
  `Õ((1/ε) (∑_ℓ c_ℓ^{1/2})^2)` (4.2); for a block-encoding observable `c_ℓ = τ_ℓ α_ℓ` (4.3).
* Direct-sampling branch: independent level estimators with variance `v_ℓ` and per-sample cost
  `τ_ℓ`; the total variance budget is `∑_ℓ v_ℓ / n_ℓ ≤ ε²`.  The optimized cost is
  `Õ((1/ε²)(∑_ℓ (τ_ℓ v_ℓ)^{1/2})^2)` (4.4), and `v_ℓ ≤ C α_ℓ²` gives the worst-case form
  `Õ((1/ε²)(∑_ℓ (τ_ℓ)^{1/2} α_ℓ)^2)` (4.5).

We formalize the exact finite-dimensional optimization behind these statements: the Titu
(Cauchy–Schwarz) lower bound over all feasible allocations, the optimal allocation attaining it,
and the two immediate instantiations (4.3), (4.4), (4.5).  The `Õ` notation of the paper is the
absorption of polylogarithmic precision factors by `τ_ℓ`; we keep the exact finite sums.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.EllipticPDELi26.MainResults.MultilevelAllocation

/-- **Lemma 4.1 (4.2), lower bound.**  For any feasible allocation `budget ℓ = ε_ℓ > 0` with
`∑_ℓ ε_ℓ ≤ ε` and nonnegative per-level costs `c_ℓ ≥ 0`, the total amplitude-estimation cost
obeys  `(1/ε) (∑_ℓ √c_ℓ)² ≤ ∑_ℓ c_ℓ / ε_ℓ`.  This is Titu's lemma (equivalently
Cauchy–Schwarz applied to `√ε_ℓ` and `√(c_ℓ/ε_ℓ)`), followed by `∑ ε_ℓ ≤ ε`. -/
theorem source_mlmc_amplitude_cost_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (c budget : ι → ℝ) (ε : ℝ) (hc : ∀ l, 0 ≤ c l) (hε : 0 < ε)
    (hbudget_pos : ∀ l, 0 < budget l) (hbudget : ∑ l, budget l ≤ ε) :
    (∑ l, Real.sqrt (c l)) ^ 2 / ε ≤ ∑ l, c l / budget l := by
  have hsum_pos : 0 < ∑ l, budget l :=
    Finset.sum_pos (fun l _ => hbudget_pos l) Finset.univ_nonempty
  have htitu : (∑ l, Real.sqrt (c l)) ^ 2 / (∑ l, budget l) ≤ ∑ l, c l / budget l := by
    have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ)
      (fun l => Real.sqrt (c l)) (g := budget) (fun l _ => hbudget_pos l)
    have hterm : (∑ l, (Real.sqrt (c l)) ^ 2 / budget l) = ∑ l, c l / budget l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Real.sq_sqrt (hc l)]
    rwa [hterm] at h
  have hmono : (∑ l, Real.sqrt (c l)) ^ 2 / ε ≤
      (∑ l, Real.sqrt (c l)) ^ 2 / (∑ l, budget l) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hsum_pos hbudget
  exact hmono.trans htitu

/-- **Lemma 4.1 (4.2), attainment.**  When every `c_ℓ > 0`, the allocation
`ε_ℓ = ε √c_ℓ / (∑_k √c_k)` is strictly positive, exhausts the budget `∑ ε_ℓ = ε`, and reaches
the lower bound `∑_ℓ c_ℓ / ε_ℓ = (∑_ℓ √c_ℓ)² / ε`.  This proves the optimized cost in (4.2) is
exactly the stated value. -/
theorem source_mlmc_amplitude_cost_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (hcpos : ∀ l, 0 < c l) (ε : ℝ) (hε : 0 < ε) :
    ∃ budget : ι → ℝ,
      (∀ l, 0 < budget l) ∧ (∑ l, budget l = ε) ∧
        (∑ l, c l / budget l = (∑ l, Real.sqrt (c l)) ^ 2 / ε) := by
  set S := ∑ l, Real.sqrt (c l) with hSdef
  have hSpos : 0 < S :=
    Finset.sum_pos (fun l _ => Real.sqrt_pos.2 (hcpos l)) Finset.univ_nonempty
  refine ⟨fun l => ε * Real.sqrt (c l) / S, ?_, ?_, ?_⟩
  · intro l
    exact div_pos (mul_pos hε (Real.sqrt_pos.2 (hcpos l))) hSpos
  · have hstep : (∑ l, ε * Real.sqrt (c l) / S) = (ε / S) * S := by
      have h1 : ∀ l, ε * Real.sqrt (c l) / S = (ε / S) * Real.sqrt (c l) := by
        intro l
        ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), ← Finset.mul_sum, ← hSdef]
    rw [hstep, div_mul_cancel₀ ε hSpos.ne']
  · have hstep : (∑ l, c l / (ε * Real.sqrt (c l) / S)) =
        ∑ l, (S / ε) * Real.sqrt (c l) := by
      apply Finset.sum_congr rfl
      intro l _
      have hc := hcpos l
      have hsq : Real.sqrt (c l) * Real.sqrt (c l) = c l := Real.mul_self_sqrt (le_of_lt hc)
      field_simp
      rw [pow_two, hsq]
    rw [hstep, ← Finset.mul_sum]
    have : (S / ε) * S = S ^ 2 / ε := by ring
    exact this

/-- **Lemma 4.1 (4.3).**  The block-encoding observable instance: with `c_ℓ = τ_ℓ α_ℓ` the
amplitude-estimation lower bound reads `(1/ε)(∑_ℓ (τ_ℓ α_ℓ)^{1/2})² ≤ ∑_ℓ τ_ℓ α_ℓ / ε_ℓ`. -/
theorem source_mlmc_block_encoding_cost_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ α budget : ι → ℝ) (ε : ℝ) (hτ : ∀ l, 0 ≤ τ l) (hα : ∀ l, 0 ≤ α l)
    (hε : 0 < ε) (hbudget_pos : ∀ l, 0 < budget l) (hbudget : ∑ l, budget l ≤ ε) :
    (∑ l, Real.sqrt (τ l * α l)) ^ 2 / ε ≤ ∑ l, τ l * α l / budget l :=
  source_mlmc_amplitude_cost_lower (fun l => τ l * α l) budget ε
    (fun l => mul_nonneg (hτ l) (hα l)) hε hbudget_pos hbudget

/-- **Lemma 4.1 (4.4).**  The direct-sampling branch: variance contributions `w_ℓ = v_ℓ / n_ℓ`
with `∑_ℓ w_ℓ ≤ ε²` give the optimized sampling cost
`(1/ε²)(∑_ℓ (τ_ℓ v_ℓ)^{1/2})² ≤ ∑_ℓ τ_ℓ v_ℓ / w_ℓ`.  This is (4.2) applied with `ε ↦ ε²`. -/
theorem source_mlmc_sampling_cost_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ v varBudget : ι → ℝ) (ε : ℝ) (hτ : ∀ l, 0 ≤ τ l) (hv : ∀ l, 0 ≤ v l)
    (hε : 0 < ε) (hbudget_pos : ∀ l, 0 < varBudget l)
    (hbudget : ∑ l, varBudget l ≤ ε ^ 2) :
    (∑ l, Real.sqrt (τ l * v l)) ^ 2 / ε ^ 2 ≤ ∑ l, τ l * v l / varBudget l :=
  source_mlmc_amplitude_cost_lower (fun l => τ l * v l) varBudget (ε ^ 2)
    (fun l => mul_nonneg (hτ l) (hv l)) (pow_pos hε 2) hbudget_pos hbudget

/-- **Lemma 4.1 (4.5), per-level scale.**  If a level-ℓ sample is bounded in magnitude so that
its variance satisfies `v_ℓ ≤ C α_ℓ²` with `C ≥ 0`, then the sampling-cost weight obeys
`√(τ_ℓ v_ℓ) ≤ √C · √τ_ℓ · α_ℓ`.  Summing this gives the worst-case bound (4.5). -/
theorem source_mlmc_sampling_scale
    (τ v C α : ℝ) (hτ : 0 ≤ τ) (hv : 0 ≤ v) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hvar : v ≤ C * α ^ 2) :
    Real.sqrt (τ * v) ≤ Real.sqrt C * Real.sqrt τ * α := by
  have hmono : Real.sqrt (τ * v) ≤ Real.sqrt (τ * (C * α ^ 2)) := by
    apply Real.sqrt_le_sqrt
    have : τ * v ≤ τ * (C * α ^ 2) := by
      exact mul_le_mul_of_nonneg_left hvar hτ
    exact this
  have hsqα : Real.sqrt (α ^ 2) = α := Real.sqrt_sq hα
  calc Real.sqrt (τ * v) ≤ Real.sqrt (τ * (C * α ^ 2)) := hmono
    _ = Real.sqrt τ * Real.sqrt (C * α ^ 2) := Real.sqrt_mul hτ (C * α ^ 2)
    _ = Real.sqrt τ * (Real.sqrt C * Real.sqrt (α ^ 2)) := by
        rw [Real.sqrt_mul hC (α ^ 2)]
    _ = Real.sqrt τ * (Real.sqrt C * α) := by rw [hsqα]
    _ = Real.sqrt C * Real.sqrt τ * α := by ring

end Qatlib.Papers.EllipticPDELi26.MainResults.MultilevelAllocation
