/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs

/-!
# Conditional resource costs from error suppression

This module converts assumed exponential lower and upper bounds on error into resource estimates
for [BhartiHaugTanggara2026]. `accuracy_dependent_cost_from_converse` gives necessary protection
and cost, while `sufficient_cost_from_suppression` selects an available integer protection size
using a logarithmic threshold.

## Main statements

* `accuracy_dependent_cost_from_converse`: An error lower bound `a * exp (-b * d^β)` together
  with error at most `ε < a` forces logarithmic lower bounds on `d` and on any resource cost
  bounded below by `cres * d^γ`.
* `sufficient_cost_from_suppression`: If available integer protection sizes approximate every
  real size above `d0` within a factor `κ`, choose one whose specified exponential error
  expression is at most `ε` and whose power-law cost satisfies the explicit logarithmic upper
  bound.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ConditionalCost
open Qatlib.Papers.SpacetimeLB26.ScalarSupport

/-- An error lower bound `a * exp (-b * d^β)` together with error at most `ε < a` forces
logarithmic lower bounds on `d` and on any resource cost bounded below by `cres * d^γ`. See
[BhartiHaugTanggara2026]. -/
theorem accuracy_dependent_cost_from_converse
    (a b cres β γ d PL Cres ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hcres : 0 < cres) (hβ : 0 < β) (hγ : 0 < γ)
    (hε0 : 0 < ε) (hεa : ε < a) (hd0 : 0 ≤ d)
    (hPL_lb : a * Real.exp (-(b * d ^ β)) ≤ PL)
    (hPL_ub : PL ≤ ε)
    (hCres : cres * d ^ γ ≤ Cres) :
    d ≥ ((1 / b) * Real.log (a / ε)) ^ (1 / β) ∧
      Cres ≥ cres * (((1 / b) * Real.log (a / ε)) ^ (γ / β)) := by
  set L : ℝ := (1 / b) * Real.log (a / ε) with hLdef
  have haratio : 0 < a / ε := div_pos ha hε0
  have hlog_pos : 0 < Real.log (a / ε) := by
    apply Real.log_pos
    rw [one_lt_div hε0]
    linarith
  have hL_nonneg : 0 ≤ L := by
    rw [hLdef]
    positivity
  have hL_pos : 0 < L := by
    rw [hLdef]
    positivity

  have hexp : Real.exp (-(b * d ^ β)) ≤ ε / a := by
    rw [le_div_iff₀ ha]
    nlinarith [hPL_lb, hPL_ub]
  have hlogexp : -(b * d ^ β) ≤ Real.log (ε / a) := by
    have := Real.log_le_log (Real.exp_pos (-(b * d ^ β))) hexp
    rwa [Real.log_exp] at this
  have hlogea : Real.log (ε / a) = -Real.log (a / ε) := by
    rw [Real.log_div (ne_of_gt hε0) (ne_of_gt ha),
        Real.log_div (ne_of_gt ha) (ne_of_gt hε0)]
    ring
  rw [hlogea] at hlogexp

  have hdβ : L ≤ d ^ β := by
    have hble : Real.log (a / ε) ≤ b * d ^ β := by linarith
    have hmul := mul_le_mul_of_nonneg_left hble (le_of_lt (inv_pos.mpr hb))
    have hrhs : b⁻¹ * (b * d ^ β) = d ^ β := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul]
    rw [hrhs] at hmul
    rw [hLdef, one_div]
    exact hmul

  have hd_ge : L ^ (1 / β) ≤ d := by
    have h := Real.rpow_le_rpow hL_nonneg hdβ (le_of_lt (one_div_pos.mpr hβ))
    rw [← Real.rpow_mul hd0, show β * (1 / β) = 1 by field_simp, Real.rpow_one] at h
    exact h

  have hdγ : L ^ (γ / β) ≤ d ^ γ := by
    have hLpow_nonneg : 0 ≤ L ^ (1 / β) := Real.rpow_nonneg hL_nonneg _
    have h := Real.rpow_le_rpow hLpow_nonneg hd_ge hγ.le
    rw [← Real.rpow_mul hL_nonneg, show (1 / β) * γ = γ / β by ring] at h
    exact h
  refine ⟨hd_ge, ?_⟩
  have := mul_le_mul_of_nonneg_left hdγ (le_of_lt hcres)
  linarith

/-- For positive `R`, multiplying `R` by `exp (-logPlus R)` gives a value at most one. -/
theorem r_mul_exp_neg_logPlus_le_one (R : ℝ) (hR : 0 < R) :
    R * Real.exp (-(logPlus R)) ≤ 1 := by
  by_cases h1 : 1 ≤ R
  · have hlog : 0 ≤ Real.log R := Real.log_nonneg h1
    rw [logPlus, max_eq_right hlog]
    have heq : R * Real.exp (-(Real.log R)) = 1 := by
      rw [Real.exp_neg, Real.exp_log hR, mul_inv_cancel₀ (ne_of_gt hR)]
    linarith
  · have hlt : R < 1 := lt_of_not_ge h1
    have hlog : Real.log R < 0 := Real.log_neg hR hlt
    rw [logPlus, max_eq_left (le_of_lt hlog), neg_zero, Real.exp_zero, mul_one]
    exact le_of_lt hlt

/-- If available integer protection sizes approximate every real size above `d0` within a factor
`κ`, choose one whose specified exponential error expression is at most `ε` and whose
power-law cost satisfies the explicit logarithmic upper bound. See [BhartiHaugTanggara2026]. -/
theorem sufficient_cost_from_suppression
    (α B β CH γ d0 κ Ccomp M ε : ℝ) (D : Set ℕ)
    (hα : 0 < α) (hB : 0 < B) (hβ : 0 < β) (hCH : 0 < CH) (hγ : 0 < γ)
    (hd0 : 1 ≤ d0) (_hκ : 1 ≤ κ) (hCcomp : 0 < Ccomp) (hM : 1 ≤ M)
    (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (havail : ∀ x : ℝ, d0 ≤ x → ∃ d ∈ D, x ≤ (d : ℝ) ∧ (d : ℝ) ≤ κ * x) :
    ∃ d : ℕ, d ∈ D ∧
      Ccomp * M * (B * Real.exp (-(α * (d : ℝ) ^ β))) ≤ ε ∧
      CH * (d : ℝ) ^ γ ≤ CH * (κ * max d0
        ((1 + (1 / α) * logPlus (Ccomp * B * M / ε)) ^ (1 / β))) ^ γ := by
  set R : ℝ := Ccomp * B * M / ε with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    positivity
  set dhat : ℝ := (1 + (1 / α) * logPlus R) ^ (1 / β) with hdhatdef
  have hbase_pos : 0 < 1 + (1 / α) * logPlus R := by
    have : 0 ≤ logPlus R := le_max_left _ _
    positivity
  set x : ℝ := max d0 dhat with hxdef

  obtain ⟨d, hdD, hxd, hdκx⟩ := havail x (le_max_left _ _)
  refine ⟨d, hdD, ?_, ?_⟩
  · have hxd' : dhat ≤ (d : ℝ) := le_trans (le_max_right _ _) hxd
    have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hdhat_nonneg : 0 ≤ dhat := Real.rpow_nonneg (le_of_lt hbase_pos) _
    have hdβ : dhat ^ β ≤ (d : ℝ) ^ β := Real.rpow_le_rpow hdhat_nonneg hxd' hβ.le
    have hαdβ : α * dhat ^ β ≤ α * (d : ℝ) ^ β :=
      mul_le_mul_of_nonneg_left hdβ hα.le
    have harg : logPlus R ≤ α * dhat ^ β := by
      have hdhatβ : dhat ^ β = 1 + (1 / α) * logPlus R := by
        rw [hdhatdef]
        rw [← Real.rpow_mul (le_of_lt hbase_pos),
          show (1 / β) * β = 1 by field_simp, Real.rpow_one]
      rw [hdhatβ]
      have hexpand : α * (1 + (1 / α) * logPlus R) = α + logPlus R := by
        rw [mul_add, mul_one, one_div, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
      rw [hexpand]
      linarith
    have hexp_le : Real.exp (-(α * (d : ℝ) ^ β)) ≤ Real.exp (-(logPlus R)) := by
      apply Real.exp_le_exp_of_le
      linarith
    have hRexp : R * Real.exp (-(logPlus R)) ≤ 1 := r_mul_exp_neg_logPlus_le_one R hRpos
    have hRe : Ccomp * B * M = R * ε := by
      rw [hRdef]; field_simp
    calc Ccomp * M * (B * Real.exp (-(α * (d : ℝ) ^ β)))
        = (Ccomp * B * M) * Real.exp (-(α * (d : ℝ) ^ β)) := by ring
      _ ≤ (Ccomp * B * M) * Real.exp (-(logPlus R)) := by
          apply mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = (R * ε) * Real.exp (-(logPlus R)) := by rw [hRe]
      _ = ε * (R * Real.exp (-(logPlus R))) := by ring
      _ ≤ ε * 1 := by
          apply mul_le_mul_of_nonneg_left hRexp hε.le
      _ = ε := by ring
  · have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hκx_nonneg : 0 ≤ κ * x := by
      have : 0 ≤ κ := by linarith
      have : 0 ≤ x := (zero_le_one.trans hd0).trans (le_max_left _ _)
      positivity
    have hpow : (d : ℝ) ^ γ ≤ (κ * x) ^ γ :=
      Real.rpow_le_rpow hdnonneg hdκx hγ.le
    have := mul_le_mul_of_nonneg_left hpow hCH.le
    simpa [hxdef] using this

end Qatlib.Papers.SpacetimeLB26.ConditionalCost
