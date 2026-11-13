/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

set_option backward.isDefEq.respectTransparency false

/-!
# The rescaled solution stays below the norm barrier

This file formalizes Lemma 3.2 of [Li and An, 2026][LiAn2026] (Section 3, p. 6; Appendix A,
pp. 22–23, Eqs. (16)–(17)): for valid Carleman parameters with `R < 1`, the rescaled initial
norm satisfies `‖u_γ(0)‖ ≤ 2R / (1 + R)` (with strict inequality whenever `‖F₀‖ > 0`), and
any scalar Riccati solution `v' = a v² - b v + c` starting in the dissipative regime
`a v₀² - b v₀ + c < 0` stays bounded above by `v₀` for all `t ≥ 0`.

## Main statements

* `lemma32_initial_norm_lt`, `lemma32_initial_norm_le`: strict and non-strict initial norm
  barrier bounds `γ x < 2R / (1 + R)` (for `c > 0`) and `γ x ≤ 2R / (1 + R)`.
* `lemma32_norm_barrier`: rescaled norm barrier bound combining non-growth with the initial
  bound.
* `lemma32_quadratic_neg`: discriminant sign `a x² - b x + c < 0` from `R < 1`.
* `lemma32_riccati_comparison`: Riccati comparison theorem proving `v t ≤ v₀` for all `t ≥ 0`.

## References

* [Li and An, 2026][LiAn2026]
-/

set_option autoImplicit false

namespace Qatlib.Papers.FastForwardLi26.CarlemanEmbed.NormBarrier

open Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel
open scoped Topology

/-- **Lemma 3.2, second inequality, nondegenerate case** ([Li and An, 2026][LiAn2026], p. 6,
Appendix A p. 23): with `γ` the smaller root of Eq. (8) and `‖F₀‖ = c > 0`,
`‖u_γ(0)‖ = γ‖u(0)‖ < 2R / (1 + R)`. -/
theorem lemma32_initial_norm_lt (p : CarlemanParams) (hp : p.Valid) (hcpos : 0 < p.c) :
    p.γ * p.x < 2 * p.R / (1 + p.R) :=
  p.gamma_mul_x_lt hp hcpos

/-- **Lemma 3.2, second inequality, boundary version**: without assuming `‖F₀‖ > 0`, the bound
holds with `≤`. -/
theorem lemma32_initial_norm_le (p : CarlemanParams) (hp : p.Valid) :
    p.γ * p.x ≤ 2 * p.R / (1 + p.R) := by
  have h := p.half_one_add_R_mul_le hp
  have hone : 0 < 1 + p.R := by
    have := p.R_pos hp
    linarith
  rw [le_div_iff₀ hone]
  nlinarith [h]

/-- **Lemma 3.2, first inequality**: combining non-growth `|u t| ≤ |u 0|` with the initial
rescaled norm bound `|u 0| = γ x < 2R / (1 + R)`. -/
theorem lemma32_norm_barrier
    (p : CarlemanParams) (hp : p.Valid) (hcpos : 0 < p.c)
    (u : ℝ → ℝ) (hnorm0 : |u 0| = p.γ * p.x)
    (hcontract : ∀ t, 0 ≤ t → |u t| ≤ |u 0|) :
    ∀ t, 0 ≤ t → |u t| ≤ |u 0| ∧ |u 0| < 2 * p.R / (1 + p.R) := by
  intro t ht
  refine ⟨hcontract t ht, ?_⟩
  rw [hnorm0]
  exact p.gamma_mul_x_lt hp hcpos

/-- **Lemma 3.2, discriminant sign** ([Li and An, 2026][LiAn2026], Appendix A, p. 23): `R < 1`
implies `a‖u(0)‖² - b‖u(0)‖ + c < 0`. -/
theorem lemma32_quadratic_neg (p : CarlemanParams) (hp : p.Valid) :
    p.a * p.x ^ 2 - p.b * p.x + p.c < 0 := by
  have h := p.R_mul_b_mul_x hp
  have hlt := hp.R_lt_one
  have hb := hp.b_pos
  have hx := hp.x_pos
  have hbx : 0 < p.b * p.x := mul_pos hb hx
  have hneg : p.R - 1 < 0 := by linarith
  have hprod : (p.R - 1) * (p.b * p.x) < 0 := mul_neg_of_neg_of_pos hneg hbx
  nlinarith [h, hprod]

/-- **Lemma 3.2, Riccati comparison step** ([Li and An, 2026][LiAn2026], Appendix A, pp. 22–23,
Eqs. (16)–(17)): if `v` solves `v' = a v² - b v + c` on `(0, ∞)` with `v(0) = v₀ > 0`,
continuous on `[0, ∞)`, where `a, c ≥ 0`, `b > 0`, and `a v₀² - b v₀ + c < 0`, then
`v(t) ≤ v₀` for all `t ≥ 0`. -/
theorem lemma32_riccati_comparison
    (a b c v0 : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (hv0 : 0 < v0) (hdisc : a * v0 ^ 2 - b * v0 + c < 0)
    (v : ℝ → ℝ) (hv_init : v 0 = v0)
    (hcont : ContinuousOn v (Set.Ici 0))
    (hsol : ∀ t, 0 < t → HasDerivAt v (a * v t ^ 2 - b * v t + c) t) :
    ∀ t, 0 ≤ t → v t ≤ v0 := by
  intro T hT0
  by_contra hnot
  push Not at hnot
  have hT_pos : 0 < T := by
    rcases eq_or_lt_of_le hT0 with rfl | hlt
    · linarith [hv_init]
    · exact hlt
  let δ : ℝ := -(a * v0 ^ 2 - b * v0 + c)
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  let denom : ℝ := 2 * a * v0 + a * (v T - v0) + b + c + 1
  have hdenom_pos : 0 < denom := by
    have ha1 : 0 ≤ 2 * a * v0 := by positivity
    have ha2 : 0 ≤ a * (v T - v0) := mul_nonneg ha (by linarith)
    dsimp [denom]
    linarith [hb, hc, hv0]
  let ε : ℝ := min ((v T - v0) / 2) (δ / (2 * denom))
  have hε_pos : 0 < ε := lt_min (by linarith) (div_pos hδ_pos (by positivity))
  have hε_lt_gap : v0 + ε < v T := by
    have hle : ε ≤ (v T - v0) / 2 := min_le_left _ _
    linarith
  have hε_quad_neg : a * (v0 + ε) ^ 2 - b * (v0 + ε) + c < 0 := by
    have hle1 : ε ≤ (v T - v0) / 2 := min_le_left _ _
    have hle2 : ε ≤ δ / (2 * denom) := min_le_right _ _
    have hlin_le : 2 * a * v0 + a * ε - b ≤ denom := by
      have haε : a * ε ≤ a * (v T - v0) := mul_le_mul_of_nonneg_left (by linarith) ha
      dsimp [denom]
      linarith [hb, hc]
    have hprod1 : ε * (2 * a * v0 + a * ε - b) ≤ ε * denom :=
      mul_le_mul_of_nonneg_left hlin_le hε_pos.le
    have hprod2 : ε * denom ≤ δ / 2 := by
      calc ε * denom ≤ (δ / (2 * denom)) * denom :=
            mul_le_mul_of_nonneg_right hle2 hdenom_pos.le
        _ = δ / 2 := by
            have hne : denom ≠ 0 := hdenom_pos.ne'
            field_simp
    have hexpand : a * (v0 + ε) ^ 2 - b * (v0 + ε) + c =
        -δ + ε * (2 * a * v0 + a * ε - b) := by
      dsimp [δ]
      ring
    linarith
  -- Extend `v` continuously to `ℝ` via `max 0` so the hitting set in `[0, T]` is compact.
  let w : ℝ → ℝ := fun t => v (max 0 t)
  have hw_cont : Continuous w :=
    hcont.comp_continuous (continuous_const.max continuous_id) (fun t => le_max_left 0 t)
  let S : Set ℝ := Set.Icc 0 T ∩ w ⁻¹' Set.Ici (v0 + ε)
  have hS_compact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_Ici.preimage hw_cont)
  have hT_mem : T ∈ S := by
    refine ⟨⟨hT0, le_refl T⟩, ?_⟩
    show v0 + ε ≤ v (max 0 T)
    rw [max_eq_right hT0]
    exact hε_lt_gap.le
  obtain ⟨tstar, htstar_mem, htstar_min⟩ :=
    hS_compact.exists_isMinOn ⟨T, hT_mem⟩ continuous_id.continuousOn
  have htstar_Icc : tstar ∈ Set.Icc 0 T := htstar_mem.1
  have htstar_ge : v0 + ε ≤ v tstar := by
    have h := htstar_mem.2
    change v0 + ε ≤ v (max 0 tstar) at h
    rwa [max_eq_right htstar_Icc.1] at h
  have htstar_pos : 0 < tstar := by
    rcases eq_or_lt_of_le htstar_Icc.1 with h0 | hlt
    · exfalso
      rw [← h0, hv_init] at htstar_ge
      linarith
    · exact hlt
  -- By the intermediate value theorem on `[0, tstar]`, `v tstar = v0 + ε`.
  have hcont_sub : ContinuousOn v (Set.Icc 0 tstar) :=
    hcont.mono (fun x hx => hx.1)
  have hivt_mem : v0 + ε ∈ Set.Icc (v 0) (v tstar) := by
    rw [hv_init]
    exact ⟨by linarith, htstar_ge⟩
  obtain ⟨s, hs_Icc, hs_eq⟩ := intermediate_value_Icc htstar_Icc.1 hcont_sub hivt_mem
  have hs_mem_S : s ∈ S := by
    refine ⟨⟨hs_Icc.1, hs_Icc.2.trans htstar_Icc.2⟩, ?_⟩
    show v0 + ε ≤ v (max 0 s)
    rw [max_eq_right hs_Icc.1, hs_eq]
  have htstar_le_s : tstar ≤ s := htstar_min hs_mem_S
  have hs_eq_tstar : s = tstar := le_antisymm hs_Icc.2 htstar_le_s
  have hv_tstar : v tstar = v0 + ε := by rwa [hs_eq_tstar] at hs_eq
  -- For `t ∈ [0, tstar)`, `t ∉ S`, so `v t < v0 + ε = v tstar`.
  have hv_le_before : ∀ u : ℝ, -tstar < u → u < 0 → v (tstar + u) ≤ v tstar := by
    intro u hu_gt hu_neg
    by_contra hgt
    push Not at hgt
    have hmem : tstar + u ∈ S := by
      refine ⟨⟨by linarith, by linarith [htstar_Icc.2]⟩, ?_⟩
      show v0 + ε ≤ v (max 0 (tstar + u))
      rw [max_eq_right (by linarith), hv_tstar] at *
      exact hgt.le
    have hmin_le : tstar ≤ tstar + u := htstar_min hmem
    linarith
  -- Take the left-hand derivative of `v` at `tstar`.
  let L : ℝ := a * v tstar ^ 2 - b * v tstar + c
  have hL_neg : L < 0 := by
    dsimp [L]
    rwa [hv_tstar]
  have hslope_tendsto := (hsol tstar htstar_pos).tendsto_slope_zero_left
  have hslope_nonneg : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 ≤ u⁻¹ • (v (tstar + u) - v tstar) := by
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr htstar_pos)] with u hu
    simp only [smul_eq_mul]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hu.2.le)
      (sub_nonpos.mpr (hv_le_before u hu.1 hu.2))
  have hL_nonneg : 0 ≤ L := ge_of_tendsto hslope_tendsto hslope_nonneg
  linarith

end Qatlib.Papers.FastForwardLi26.CarlemanEmbed.NormBarrier
