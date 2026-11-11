/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Appendix B: the `Δ`-region arithmetic

Source: arXiv:2105.02859v3, Sec. V A 2 and Appendix B, Lemma 13
(Eqs. (B14)--(B16)) and Theorem 8 (Eqs. (70)/(B13), (B17)--(B18)).

The QSVT sign-function approximation used by the paper's phase estimation
fails on the "`Δ`-region" `[1/√2 − Δ/2, 1/√2 + Δ/2]`.  This file isolates the
pure real-trigonometry behind the region analysis, so that both the Theorem 8
and the Lemma 13 paper-layer statements can share it:

* `cos_pi_div_four_sub_add` / `cos3_plus_cos5_lt_sqrt_two`: the strict
  inequality `cos(3π/16) + cos(5π/16) < √2` which makes the constant
  `2 (cos(3π/16) − 1/√2)` of Eq. (70) sufficient for condition (B16);
* `arccos_bounds_of_B16`: under (B16),
  `3π/16 < arccos(1/√2 + Δ/2)` and `arccos(1/√2 − Δ/2) < 5π/16`, i.e. a
  `Δ`-region hit forces the deviation into
  `(3/16, 5/16) ∪ (11/16, 13/16)` (paper Fig. 18);
* `region_bounds`: the per-branch `arccos` argument for one branch of
  `|0.φ[j+1:] − θ| ∈ [0, 1/2]` — the two branches correspond to
  `θ = 0` and `θ = 1` in paper Fig. 18.

Boundary: pure real trigonometry; no QSVT, measurement or algorithm model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

open scoped Real

/-- `cos (π/4 - t) + cos (π/4 + t) = √2 cos t` (sum-to-product at `π/4`). -/
lemma cos_pi_div_four_sub_add (t : ℝ) :
    Real.cos (π / 4 - t) + Real.cos (π / 4 + t) = Real.sqrt 2 * Real.cos t := by
  rw [Real.cos_sub, Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

/-- The strict inequality `cos (3π/16) + cos (5π/16) < √2` behind the constant
of Eq. (70): `3π/16` and `5π/16` are symmetric around `π/4`. -/
lemma cos3_plus_cos5_lt_sqrt_two :
    Real.cos (3 * π / 16) + Real.cos (5 * π / 16) < Real.sqrt 2 := by
  have h := cos_pi_div_four_sub_add (π / 16)
  have h3 : 3 * π / 16 = π / 4 - π / 16 := by ring
  have h5 : 5 * π / 16 = π / 4 + π / 16 := by ring
  rw [h3, h5, h]
  have hcos : Real.cos (π / 16) < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one (π / 16)) with h' | h'
    · exact h'
    · exfalso
      have hx := (Real.cos_eq_one_iff_of_lt_of_lt (x := π / 16)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h'
      linarith [Real.pi_pos]
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- Lemma 13 hypothesis (B16) converted into the two `arccos` bounds that
localize the `Δ`-region: `3π/16 < arccos(1/√2 + Δ/2)` and
`arccos(1/√2 − Δ/2) < 5π/16`. -/
lemma arccos_bounds_of_B16 {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hB16 : 1 / 4 - (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) < 1 / 16) :
    3 * π / 16 < Real.arccos (1 / Real.sqrt 2 + Δ / 2) ∧
      Real.arccos (1 / Real.sqrt 2 - Δ / 2) < 5 * π / 16 := by
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hcpos : 0 < 1 / Real.sqrt 2 := by positivity
  have hcle : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hA1gt : 3 * π / 16 < Real.arccos (1 / Real.sqrt 2 + Δ / 2) := by
    have h1 : 1 / 4 - 1 / 16 < (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) := by
      linarith
    have h2 : (1 / 4 - 1 / 16) * π < Real.arccos (1 / Real.sqrt 2 + Δ / 2) := by
      have hm := mul_lt_mul_of_pos_right h1 hpi0
      have hs : (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) * π
          = Real.arccos (1 / Real.sqrt 2 + Δ / 2) := by
        field_simp
      linarith [hm, hs]
    have h3 : (1 / 4 - 1 / 16) * π = 3 * π / 16 := by ring
    linarith
  have hxcos_lt : 1 / Real.sqrt 2 + Δ / 2 < Real.cos (3 * π / 16) := by
    have hxle1 : 1 / Real.sqrt 2 + Δ / 2 < 1 :=
      Real.arccos_pos.mp (by linarith)
    have hxge : -1 ≤ 1 / Real.sqrt 2 + Δ / 2 := by linarith
    have hcosval : Real.cos (Real.arccos (1 / Real.sqrt 2 + Δ / 2))
        = 1 / Real.sqrt 2 + Δ / 2 := Real.cos_arccos hxge hxle1.le
    have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 3 * π / 16) (y := Real.arccos (1 / Real.sqrt 2 + Δ / 2)) (by positivity)
      (Real.arccos_le_pi _) hA1gt
    rwa [hcosval] at hcoslt
  have hδ : Δ / 2 < Real.cos (3 * π / 16) - 1 / Real.sqrt 2 := by linarith
  have hsum : Real.cos (3 * π / 16) + Real.cos (5 * π / 16) < 2 * (1 / Real.sqrt 2) := by
    have h2c : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
      have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp
      rw [pow_two, Real.mul_self_sqrt (by norm_num)]
    have h := cos3_plus_cos5_lt_sqrt_two
    linarith
  refine ⟨hA1gt, ?_⟩
  have hxgt : Real.cos (5 * π / 16) < 1 / Real.sqrt 2 - Δ / 2 := by linarith
  have hxle1 : 1 / Real.sqrt 2 - Δ / 2 ≤ 1 := by linarith
  have hcoslt := Real.arccos_lt_arccos
    (x := Real.cos (5 * π / 16)) (y := 1 / Real.sqrt 2 - Δ / 2)
    (Real.neg_one_le_cos _) hxgt hxle1
  have h5 : Real.arccos (Real.cos (5 * π / 16)) = 5 * π / 16 :=
    Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
  rwa [h5] at hcoslt

/-- One branch of the `Δ`-region localization (paper Fig. 18): for a deviation
`w ∈ [0, 1/2]` (the `θ = 0` branch), a `Δ`-region hit forces
`3/16 < w < 5/16`.  The same statement with `w = 1 − |y|` gives the `θ = 1`
branch `11/16 < |y| < 13/16`. -/
lemma region_bounds {Δ c A₁ A₂ : ℝ}
    (hA₁ : A₁ = Real.arccos (c + Δ / 2)) (hA₂ : A₂ = Real.arccos (c - Δ / 2))
    (hA1gt : 3 * π / 16 < A₁) (hA2lt : A₂ < 5 * π / 16)
    {w : ℝ} (hw0 : 0 ≤ w) (hwhalf : w ≤ 1 / 2)
    (hreg : |Real.cos (π * w)| ∈ Set.Icc (c - Δ / 2) (c + Δ / 2)) :
    3 / 16 < w ∧ w < 5 / 16 := by
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hpiw0 : 0 ≤ π * w := by positivity
  have hpiwpi : π * w ≤ π := by nlinarith
  have hcos_nonneg : 0 ≤ Real.cos (π * w) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> nlinarith
  have hcos_abs : |Real.cos (π * w)| = Real.cos (π * w) := abs_of_nonneg hcos_nonneg
  have hle : Real.cos (π * w) ≤ c + Δ / 2 := by
    have := hreg.2
    rwa [hcos_abs] at this
  have hge : c - Δ / 2 ≤ Real.cos (π * w) := by
    have := hreg.1
    rwa [hcos_abs] at this
  have hA1le : A₁ ≤ π * w := by
    have h := Real.arccos_le_arccos (x := Real.cos (π * w)) (y := c + Δ / 2) hle
    simpa [hA₁, Real.arccos_cos hpiw0 hpiwpi] using h
  have hA2ge : π * w ≤ A₂ := by
    have h := Real.arccos_le_arccos (x := c - Δ / 2) (y := Real.cos (π * w)) hge
    simpa [hA₂, Real.arccos_cos hpiw0 hpiwpi] using h
  have h1 : 3 * π / 16 < π * w := lt_of_lt_of_le hA1gt hA1le
  have h2 : π * w < 5 * π / 16 := lt_of_le_of_lt hA2ge hA2lt
  constructor
  · have hmul : (3 / 16 : ℝ) * π < w * π := by
      calc (3 / 16 : ℝ) * π = 3 * π / 16 := by ring
        _ < π * w := h1
        _ = w * π := by ring
    exact lt_of_mul_lt_mul_right hmul hpi0.le
  · have hmul : w * π < (5 / 16 : ℝ) * π := by
      calc w * π = π * w := by ring
        _ < 5 * π / 16 := h2
        _ = (5 / 16 : ℝ) * π := by ring
    exact lt_of_mul_lt_mul_right hmul hpi0.le

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
