/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
# The second-order crossing location

This module defines an eventual comparison relation `ThetaAtTop` and its elementary closure
properties. For the second-order energy models `energyL` and `energyU`, it proves an explicit
crossing and derives the location scale `n^(-1/4) * (m/n)^(3/4)` under the stated asymptotic and
positivity assumptions, as in [FarhiEtAl2011].

## Main statements

* `crossing_second_order`: equality of the two energy models at an explicit value of `sStarOf`.
* `inv_sqrt_gapScale_eq_paperScale`: the identity relating the two scale formulas.
* `gap_location_theta`: the eventual scale of one minus the crossing parameter.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option autoImplicit false
noncomputable section

open Filter

namespace Qatlib.Papers.AdiabGaps09.MainResults

/-- Eventual two-sided comparison of `f` with positive constant multiples of `g` along the
natural numbers tending to infinity. -/
def ThetaAtTop (f g : ℕ → ℝ) : Prop :=
  ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∀ᶠ n in Filter.atTop, b * g n ≤ f n ∧ f n ≤ c * g n

/-- Every function satisfies the eventual comparison relation `ThetaAtTop` with itself. -/
theorem ThetaAtTop.refl (f : ℕ → ℝ) : ThetaAtTop f f :=
  ⟨1, 1, one_pos, one_pos,
    Eventually.of_forall (fun n => ⟨by rw [one_mul], by rw [one_mul]⟩)⟩

/-- The eventual comparison relation `ThetaAtTop` is transitive. -/
theorem ThetaAtTop.trans {f g h : ℕ → ℝ} (hfg : ThetaAtTop f g)
    (hgh : ThetaAtTop g h) : ThetaAtTop f h := by
  obtain ⟨b1, c1, hb1, hc1, h1⟩ := hfg
  obtain ⟨b2, c2, hb2, hc2, h2⟩ := hgh
  refine ⟨b1 * b2, c1 * c2, mul_pos hb1 hb2, mul_pos hc1 hc2, ?_⟩
  filter_upwards [h1, h2] with n hn1 hn2
  constructor
  · calc b1 * b2 * h n = b1 * (b2 * h n) := by ring
      _ ≤ b1 * g n := by nlinarith [hn2.1]
      _ ≤ f n := hn1.1
  · calc f n ≤ c1 * g n := hn1.2
      _ ≤ c1 * (c2 * h n) := by nlinarith [hn2.2]
      _ = c1 * c2 * h n := by ring

/-- Multiplying the first function by a positive real constant preserves its `ThetaAtTop`
comparison with the second function. -/
theorem ThetaAtTop.const_mul {f g : ℕ → ℝ} (a : ℝ) (ha : 0 < a)
    (h : ThetaAtTop f g) : ThetaAtTop (fun n => a * f n) g := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := h
  refine ⟨a * b, a * c, mul_pos ha hb, mul_pos ha hc, ?_⟩
  filter_upwards [hbnd] with n hn
  constructor
  · calc a * b * g n = a * (b * g n) := by ring
      _ ≤ a * f n := by nlinarith [hn.1]
  · calc a * f n ≤ a * (c * g n) := by nlinarith [hn.2]
      _ = a * c * g n := by ring

/-- Taking square roots preserves `ThetaAtTop` when both functions are eventually nonnegative. -/
theorem ThetaAtTop.sqrt {f g : ℕ → ℝ} (h : ThetaAtTop f g)
    (hf : ∀ᶠ n in Filter.atTop, 0 ≤ f n) (hg : ∀ᶠ n in Filter.atTop, 0 ≤ g n) :
    ThetaAtTop (fun n => Real.sqrt (f n)) (fun n => Real.sqrt (g n)) := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := h
  refine ⟨Real.sqrt b, Real.sqrt c, Real.sqrt_pos.mpr hb, Real.sqrt_pos.mpr hc, ?_⟩
  filter_upwards [hbnd, hf, hg] with n hn _ _
  constructor
  · rw [← Real.sqrt_mul (le_of_lt hb)]
    exact Real.sqrt_le_sqrt hn.1
  · rw [← Real.sqrt_mul (le_of_lt hc)]
    exact Real.sqrt_le_sqrt hn.2

/-- Taking reciprocals preserves `ThetaAtTop` when both functions are eventually positive. -/
theorem ThetaAtTop.inv {f g : ℕ → ℝ} (h : ThetaAtTop f g)
    (hf : ∀ᶠ n in Filter.atTop, 0 < f n) (hg : ∀ᶠ n in Filter.atTop, 0 < g n) :
    ThetaAtTop (fun n => (f n)⁻¹) (fun n => (g n)⁻¹) := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := h
  refine ⟨c⁻¹, b⁻¹, inv_pos.mpr hc, inv_pos.mpr hb, ?_⟩
  filter_upwards [hbnd, hf, hg] with n hn hfn hgn
  constructor
  · have := (inv_le_inv₀ (mul_pos hc hgn) hfn).mpr hn.2
    simpa [mul_inv, mul_comm] using this
  · have := (inv_le_inv₀ hfn (mul_pos hb hgn)).mpr hn.1
    simpa [mul_inv, mul_comm] using this

/-- The second function in a `ThetaAtTop` relation can be replaced by an eventually equal
function. -/
theorem ThetaAtTop.of_eventuallyEq_right {f g h : ℕ → ℝ} (hfg : ThetaAtTop f g)
    (hgh : ∀ᶠ n in Filter.atTop, g n = h n) : ThetaAtTop f h := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := hfg
  refine ⟨b, c, hb, hc, ?_⟩
  filter_upwards [hbnd, hgh] with n hn heq
  rw [← heq]; exact hn

/-- The first function in a `ThetaAtTop` relation can be replaced by an eventually equal
function. -/
theorem ThetaAtTop.of_eventuallyEq_left {f g h : ℕ → ℝ} (hfg : ThetaAtTop f g)
    (hfh : ∀ᶠ n in Filter.atTop, f n = h n) : ThetaAtTop h g := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := hfg
  refine ⟨b, c, hb, hc, ?_⟩
  filter_upwards [hbnd, hfh] with n hn heq
  rw [← heq]; exact hn

/-- The second-order energy expression `(1 - s) * n/2 + s * (((1 - s)/s)² * e2)`. -/
def energyL (n e2 s : ℝ) : ℝ :=
  (1 - s) * (n / 2) + s * (((1 - s) / s) ^ 2 * e2)

/-- The second-order energy expression with the additional contribution `s/2` relative to
`energyL n e2 s`. -/
def energyU (n e2 s : ℝ) : ℝ :=
  (1 - s) * (n / 2) + s * ((1 / 2) + ((1 - s) / s) ^ 2 * e2)

/-- The parameter `1 / (1 + δ)` used to express a second-order crossing location. -/
def sStarOf (δ : ℝ) : ℝ := 1 / (1 + δ)

/-- The difference of the lower and upper energy expressions is `s * (-1/2 + ((1 - s)/s)² * (eL
- eU))`. See [FarhiEtAl2011]. -/
theorem energy_diff (n eL eU s : ℝ) :
    energyL n eL s - energyU n eU s
      = s * (-(1 / 2) + ((1 - s) / s) ^ 2 * (eL - eU)) := by
  unfold energyL energyU
  ring

/-- If `eL - eU` is positive, the two second-order energy expressions coincide at `sStarOf (1 /
sqrt(2 * (eL - eU)))`. See [FarhiEtAl2011]. -/
theorem crossing_second_order (n eL eU : ℝ) (hD : 0 < eL - eU) :
    energyL n eL (sStarOf (1 / Real.sqrt (2 * (eL - eU))))
      = energyU n eU (sStarOf (1 / Real.sqrt (2 * (eL - eU)))) := by
  set D := eL - eU with hDdef
  have h2D : 0 < 2 * D := by rw [hDdef]; positivity
  have hsqne : Real.sqrt (2 * D) ≠ 0 := (Real.sqrt_pos.mpr h2D).ne'
  have hδ : (1 - sStarOf (1 / Real.sqrt (2 * D))) / sStarOf (1 / Real.sqrt (2 * D))
      = 1 / Real.sqrt (2 * D) := by
    unfold sStarOf
    field_simp
    ring
  have hsq2 : (1 / Real.sqrt (2 * D)) ^ 2 * D = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h2D)]
    field_simp
  have hdiff : energyL n eL (sStarOf (1 / Real.sqrt (2 * D)))
      - energyU n eU (sStarOf (1 / Real.sqrt (2 * D))) = 0 := by
    rw [energy_diff]
    rw [show eL - eU = D from hDdef.symm, hδ, hsq2]
    ring
  exact sub_eq_zero.mp hdiff

/-- The scale `sqrt(n) * (n / m n) * sqrt(n / m n)` for the second-order coefficient difference. -/
def gapScale (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * ((n : ℝ) / m n) * Real.sqrt ((n : ℝ) / m n)

/-- The scale `n^(-1/4) * (m n / n)^(3/4)` for the distance of the crossing parameter from one. -/
def paperScale (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 4 : ℝ)) * (m n / (n : ℝ)) ^ ((3 / 4 : ℝ))

/-- For positive `m n` and `n`, the reciprocal square root of `gapScale m n` equals `paperScale
m n`. See [FarhiEtAl2011]. -/
theorem inv_sqrt_gapScale_eq_paperScale (m : ℕ → ℝ) (n : ℕ)
    (hm : 0 < m n) (hn : 0 < (n : ℝ)) :
    (Real.sqrt (gapScale m n))⁻¹ = paperScale m n := by
  have hN : (0 : ℝ) < (n : ℝ) := hn
  have hM : (0 : ℝ) < m n := hm
  have hr : (0 : ℝ) < (n : ℝ) / m n := div_pos hN hM

  have hg : gapScale m n
      = (n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) / m n) ^ ((3 : ℝ) / 2) := by
    unfold gapScale
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hsplit : ((n : ℝ) / m n) ^ ((3 : ℝ) / 2)
        = ((n : ℝ) / m n) ^ (1 : ℝ) * ((n : ℝ) / m n) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hr]
      norm_num
    rw [hsplit, Real.rpow_one]
    ring

  have hs : Real.sqrt (gapScale m n)
      = (n : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) / m n) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, hg]
    rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hr.le _)]
    rw [← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
    norm_num
  rw [hs]

  rw [mul_inv, ← Real.rpow_neg hN.le, ← Real.rpow_neg hr.le]
  unfold paperScale
  congr 1

  have hMN : m n / (n : ℝ) = ((n : ℝ) / m n)⁻¹ := (inv_div (n : ℝ) (m n)).symm
  rw [hMN, Real.inv_rpow hr.le, Real.rpow_neg hr.le]

/-- If `δ` has `ThetaAtTop` scale `h` and eventually lies in `(0, 1]`, then `1 - sStarOf (δ n)`
has the same scale. See [FarhiEtAl2011]. -/
theorem one_minus_sStar_theta {δ h : ℕ → ℝ} (hδ : ThetaAtTop δ h)
    (hδpos : ∀ᶠ n in Filter.atTop, 0 < δ n) (hbdd : ∀ᶠ n in Filter.atTop, δ n ≤ 1) :
    ThetaAtTop (fun n => 1 - sStarOf (δ n)) h := by
  have hself : ThetaAtTop (fun n => 1 - sStarOf (δ n)) δ := by
    refine ⟨1 / 2, 1, by norm_num, one_pos, ?_⟩
    filter_upwards [hδpos, hbdd] with n hpos hle
    have hden : 0 < 1 + δ n := by linarith
    have hkey : 1 - sStarOf (δ n) = δ n / (1 + δ n) := by
      unfold sStarOf
      field_simp
      ring
    rw [hkey]
    constructor
    · rw [le_div_iff₀ hden]
      nlinarith
    · rw [div_le_iff₀ hden]
      nlinarith
  exact hself.trans hδ

/-- Under the stated eventual positivity, comparison, and boundedness assumptions, `1 - sStarOf
(1 / sqrt(2 * D n))` has `ThetaAtTop` scale `paperScale m`. See [FarhiEtAl2011]. -/
theorem gap_location_theta (m D : ℕ → ℝ)
    (hm : ∀ᶠ n in Filter.atTop, 0 < m n) (hn : ∀ᶠ n : ℕ in Filter.atTop, 0 < (n : ℝ))
    (hDpos : ∀ᶠ n in Filter.atTop, 0 < D n) (hgpos : ∀ᶠ n in Filter.atTop, 0 < gapScale m n)
    (hD : ThetaAtTop D (gapScale m))
    (hbdd : ∀ᶠ n in Filter.atTop, 1 / Real.sqrt (2 * D n) ≤ 1) :
    ThetaAtTop (fun n => 1 - sStarOf (1 / Real.sqrt (2 * D n))) (paperScale m) := by

  have hstep1 : ThetaAtTop (fun n => 1 / Real.sqrt (2 * D n))
      (fun n => (Real.sqrt (D n))⁻¹) := by
    have hconst : ThetaAtTop (fun n => (1 / Real.sqrt 2) * (Real.sqrt (D n))⁻¹)
        (fun n => (Real.sqrt (D n))⁻¹) :=
      ThetaAtTop.const_mul (1 / Real.sqrt 2) (by positivity)
        (ThetaAtTop.refl (fun n => (Real.sqrt (D n))⁻¹))
    refine ThetaAtTop.of_eventuallyEq_left hconst ?_
    filter_upwards [hDpos] with n _
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), one_div, one_div, mul_inv]

  have hstep2 : ThetaAtTop (fun n => (Real.sqrt (D n))⁻¹)
      (fun n => (Real.sqrt (gapScale m n))⁻¹) :=
    (hD.sqrt (hDpos.mono (fun n h => le_of_lt h))
        (hgpos.mono (fun n h => le_of_lt h))).inv
      (hDpos.mono (fun n h => Real.sqrt_pos.mpr h))
      (hgpos.mono (fun n h => Real.sqrt_pos.mpr h))

  have hstep3 : ThetaAtTop (fun n => (Real.sqrt (gapScale m n))⁻¹) (paperScale m) := by
    refine ThetaAtTop.of_eventuallyEq_right (ThetaAtTop.refl _) ?_
    filter_upwards [hm, hn] with n hmn hnn
    exact inv_sqrt_gapScale_eq_paperScale m n hmn hnn
  have hδg : ThetaAtTop (fun n => 1 / Real.sqrt (2 * D n)) (paperScale m) :=
    hstep1.trans (hstep2.trans hstep3)
  refine one_minus_sStar_theta hδg ?_ hbdd
  filter_upwards [hDpos] with n hDn
  have h2D : 0 < 2 * D n := by positivity
  exact one_div_pos.mpr (Real.sqrt_pos.mpr h2D)

end Qatlib.Papers.AdiabGaps09.MainResults
