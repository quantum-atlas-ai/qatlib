/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QIntegration00.MainResults.Defs
set_option warningAsError false

noncomputable section

set_option autoImplicit false

namespace Qatlib.Papers.QIntegration00.MainResults.CoinMonteCarloUpper

open Defs

theorem coin_upper_bound_at {γ C c : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hc : 0 < c)
    {cost error : ℝ → ℝ} (hcost_nn : ∀ t, 0 ≤ cost t)
    {t ε : ℝ} (ht0 : 0 < t) (hL1 : 1 ≤ Real.log t⁻¹)
    (hcost : cost t ≤ C * t⁻¹ ^ 2 * Real.log t⁻¹)
    (herror : error t ≤ c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ))
    (hbal : c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ) = ε)
    (hε : 0 < ε) (hεc : ε ≤ 1 / c) (hε2 : ε ≤ 1 / 2) :
    complexityOf cost error ε ≤
      C * c ^ (2 / (1 + 2 * γ)) * (2 / (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) *
        ε ^ (-2 / (1 + 2 * γ)) * (Real.log ε⁻¹) ^ (1 / (1 + 2 * γ)) := by
  have hs1 : (0 : ℝ) < 1 + 2 * γ := by linarith
  have hsne : (1 + 2 * γ) ≠ 0 := ne_of_gt hs1
  set L : ℝ := Real.log t⁻¹ with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLp : 0 < L ^ γ := Real.rpow_pos_of_pos hLpos γ
  have hx : 0 < ε / c := div_pos hε hc
  have hcx : 0 < c / ε := div_pos hc hε

  have herrt : error t ≤ ε := by
    rw [← hbal]
    exact herror

  have hneg : L ^ (-γ) = (L ^ γ)⁻¹ := Real.rpow_neg (le_of_lt hLpos) γ
  have hA : t ^ (1 + 2 * γ) = (ε / c) * L ^ γ := by
    have hcancel : L ^ (-γ) * L ^ γ = 1 := by
      rw [hneg]
      exact inv_mul_cancel₀ (ne_of_gt hLp)
    have hmul : c * t ^ (1 + 2 * γ) * L ^ (-γ) * L ^ γ = ε * L ^ γ := by
      rw [hbal]
    have hstep : c * t ^ (1 + 2 * γ) = ε * L ^ γ := by
      calc c * t ^ (1 + 2 * γ) = c * t ^ (1 + 2 * γ) * (L ^ (-γ) * L ^ γ) := by
            rw [hcancel, mul_one]
        _ = c * t ^ (1 + 2 * γ) * L ^ (-γ) * L ^ γ := by ring
        _ = ε * L ^ γ := hmul
    field_simp
    linarith [hstep]

  have htr : (t ^ (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) = t := by
    rw [← Real.rpow_mul (le_of_lt ht0)]
    have hexp : (1 + 2 * γ) * (1 / (1 + 2 * γ)) = 1 := by
      field_simp
    rw [hexp, Real.rpow_one]
  have ht_eq : t = (ε / c) ^ (1 / (1 + 2 * γ)) * L ^ (γ / (1 + 2 * γ)) := by
    calc t = (t ^ (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) := htr.symm
      _ = ((ε / c) * L ^ γ) ^ (1 / (1 + 2 * γ)) := by rw [hA]
      _ = (ε / c) ^ (1 / (1 + 2 * γ)) * (L ^ γ) ^ (1 / (1 + 2 * γ)) :=
            Real.mul_rpow (le_of_lt hx) (le_of_lt hLp)
      _ = (ε / c) ^ (1 / (1 + 2 * γ)) * L ^ (γ * (1 / (1 + 2 * γ))) := by
            rw [Real.rpow_mul (le_of_lt hLpos)]
      _ = (ε / c) ^ (1 / (1 + 2 * γ)) * L ^ (γ / (1 + 2 * γ)) := by
            congr 2
            ring

  have htinv : t⁻¹ = (c / ε) ^ (1 / (1 + 2 * γ)) * L ^ (-γ / (1 + 2 * γ)) := by
    rw [ht_eq, mul_inv]
    congr 1
    · rw [(Real.inv_rpow (le_of_lt hx) (1 / (1 + 2 * γ))).symm]
      congr 1
      field_simp
    · rw [← Real.rpow_neg (le_of_lt hLpos)]
      congr 1
      ring

  have htinv_sq : t⁻¹ ^ 2 =
      (c / ε) ^ (2 / (1 + 2 * γ)) * L ^ (-2 * γ / (1 + 2 * γ)) := by
    rw [htinv, mul_pow]
    congr 1
    · rw [← Real.rpow_natCast ((c / ε) ^ (1 / (1 + 2 * γ))) 2,
          ← Real.rpow_mul (le_of_lt hcx)]
      congr 1
      ring
    · rw [← Real.rpow_natCast (L ^ (-γ / (1 + 2 * γ))) 2,
          ← Real.rpow_mul (le_of_lt hLpos)]
      congr 1
      ring
  have hexpL : L ^ (-2 * γ / (1 + 2 * γ)) * L = L ^ (1 / (1 + 2 * γ)) := by
    calc L ^ (-2 * γ / (1 + 2 * γ)) * L = L ^ (-2 * γ / (1 + 2 * γ)) * L ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = L ^ (-2 * γ / (1 + 2 * γ) + 1) := (Real.rpow_add hLpos _ _).symm
      _ = L ^ (1 / (1 + 2 * γ)) := by
          congr 1
          field_simp
          ring
  have hcost1 : cost t ≤ C * (c / ε) ^ (2 / (1 + 2 * γ)) * L ^ (1 / (1 + 2 * γ)) := by
    calc cost t ≤ C * t⁻¹ ^ 2 * L := hcost
      _ = C * ((c / ε) ^ (2 / (1 + 2 * γ)) * L ^ (-2 * γ / (1 + 2 * γ))) * L := by
            rw [htinv_sq]
      _ = C * (c / ε) ^ (2 / (1 + 2 * γ)) * (L ^ (-2 * γ / (1 + 2 * γ)) * L) := by ring
      _ = C * (c / ε) ^ (2 / (1 + 2 * γ)) * L ^ (1 / (1 + 2 * γ)) := by rw [hexpL]
  have hdiv : (c / ε) ^ (2 / (1 + 2 * γ)) =
      c ^ (2 / (1 + 2 * γ)) * ε ^ (-2 / (1 + 2 * γ)) := by
    rw [Real.div_rpow (le_of_lt hc) (le_of_lt hε), div_eq_mul_inv]
    have hepsneg : (ε ^ (2 / (1 + 2 * γ)))⁻¹ = ε ^ (-2 / (1 + 2 * γ)) := by
      rw [← Real.rpow_neg (le_of_lt hε)]
      congr 1
      ring
    rw [hepsneg]

  have hLg : 1 ≤ L ^ γ := Real.one_le_rpow hL1 (le_of_lt hγ)
  have hxc_le : ε / c ≤ t ^ (1 + 2 * γ) := by
    rw [hA]
    calc ε / c = (ε / c) * 1 := by ring
      _ ≤ (ε / c) * L ^ γ := mul_le_mul_of_nonneg_left hLg (le_of_lt hx)
  have htge : (ε / c) ^ (1 / (1 + 2 * γ)) ≤ t := by
    calc (ε / c) ^ (1 / (1 + 2 * γ)) ≤ (t ^ (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) :=
          Real.rpow_le_rpow (le_of_lt hx) hxc_le (by positivity)
      _ = t := htr
  have hc_inv : c ≤ ε⁻¹ := by
    have hcε : c * ε ≤ 1 := by
      have h1 : ε ≤ 1 / c := hεc
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
      rw [mul_one_div, div_self (ne_of_gt hc)] at this
      linarith [this]
    rw [← one_div]
    exact (le_div_iff₀ hε).mpr hcε
  have hLle : L ≤ (2 / (1 + 2 * γ)) * Real.log ε⁻¹ := by
    have htinv_le : t⁻¹ ≤ (c / ε) ^ (1 / (1 + 2 * γ)) := by
      have hinv : ((ε / c) ^ (1 / (1 + 2 * γ)))⁻¹ = (c / ε) ^ (1 / (1 + 2 * γ)) := by
        rw [(Real.inv_rpow (le_of_lt hx) (1 / (1 + 2 * γ))).symm]
        congr 1
        field_simp
      have hpos : 0 < (ε / c) ^ (1 / (1 + 2 * γ)) := Real.rpow_pos_of_pos hx _
      calc t⁻¹ ≤ ((ε / c) ^ (1 / (1 + 2 * γ)))⁻¹ := inv_anti₀ hpos htge
        _ = (c / ε) ^ (1 / (1 + 2 * γ)) := hinv
    have hlog : L ≤ Real.log ((c / ε) ^ (1 / (1 + 2 * γ))) := by
      rw [hLdef]
      exact Real.log_le_log (inv_pos.mpr ht0) htinv_le
    have hlog2 : Real.log ((c / ε) ^ (1 / (1 + 2 * γ))) =
        (1 / (1 + 2 * γ)) * (Real.log c + Real.log ε⁻¹) := by
      rw [Real.log_rpow (by positivity)]
      congr 1
      have hcne : c ≠ 0 := ne_of_gt hc
      have hene : ε ≠ 0 := ne_of_gt hε
      rw [div_eq_mul_inv, Real.log_mul hcne (inv_ne_zero hene)]
    have hlogc : Real.log c ≤ Real.log ε⁻¹ := Real.log_le_log hc hc_inv
    have hsum : Real.log c + Real.log ε⁻¹ ≤ 2 * Real.log ε⁻¹ := by linarith
    have hnonneg : 0 ≤ 1 / (1 + 2 * γ) := by positivity
    calc L ≤ (1 / (1 + 2 * γ)) * (Real.log c + Real.log ε⁻¹) := by
            rw [← hlog2]; exact hlog
      _ ≤ (1 / (1 + 2 * γ)) * (2 * Real.log ε⁻¹) :=
            mul_le_mul_of_nonneg_left hsum hnonneg
      _ = (2 / (1 + 2 * γ)) * Real.log ε⁻¹ := by ring
  have hlogε_pos : 0 < Real.log ε⁻¹ := by
    have hε1 : ε < 1 := by linarith
    exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨hε, hε1⟩)

  calc complexityOf cost error ε ≤ cost t := complexityOf_le hcost_nn ht0 herrt
    _ ≤ C * (c / ε) ^ (2 / (1 + 2 * γ)) * L ^ (1 / (1 + 2 * γ)) := hcost1
    _ = C * (c ^ (2 / (1 + 2 * γ)) * ε ^ (-2 / (1 + 2 * γ))) *
          L ^ (1 / (1 + 2 * γ)) := by
          rw [hdiv]
    _ ≤ C * (c ^ (2 / (1 + 2 * γ)) * ε ^ (-2 / (1 + 2 * γ))) *
          ((2 / (1 + 2 * γ)) * Real.log ε⁻¹) ^ (1 / (1 + 2 * γ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (le_of_lt hLpos) hLle (by positivity)
    _ = C * c ^ (2 / (1 + 2 * γ)) * (2 / (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) *
          ε ^ (-2 / (1 + 2 * γ)) * (Real.log ε⁻¹) ^ (1 / (1 + 2 * γ)) := by
          rw [Real.mul_rpow (by positivity) (le_of_lt hlogε_pos)]
          ring

theorem coin_upper_bound {γ C c : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hc : 0 < c)
    {cost error : ℝ → ℝ} (hcost_nn : ∀ t, 0 ≤ cost t)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) 1, cost t ≤ C * t⁻¹ ^ 2 * Real.log t⁻¹)
    (herror : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      error t ≤ c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ))
    (hsel : CoinSelection γ c) :
    IsCoinUpper γ (C * c ^ (2 / (1 + 2 * γ)) * (2 / (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)))
      (complexityOf cost error) := by
  intro ε hεmem
  obtain ⟨hε, hε2⟩ := hεmem
  obtain ⟨t, ht0, ht1, hL1, hbal, hεc⟩ := hsel ε ⟨hε, hε2⟩
  have hcostt := hcost t ⟨ht0, ht1⟩
  have herrt := herror t ⟨ht0, ht1⟩
  simpa [IsCoinUpper, coinExponent, coinLogExponent] using
    (coin_upper_bound_at hγ hC hc hcost_nn ht0 hL1 hcostt herrt hbal hε hεc hε2)

theorem coin_upper_bound_small {γ C c : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hc : 0 < c)
    {cost error : ℝ → ℝ} (hcost_nn : ∀ t, 0 ≤ cost t)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) 1, cost t ≤ C * t⁻¹ ^ 2 * Real.log t⁻¹)
    (herror : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      error t ≤ c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ)) :
    ∀ ε ∈ Set.Ioc (0 : ℝ) (min (1 / 2) (min (1 / c) (c * Real.exp (-(1 + 2 * γ))))),
      complexityOf cost error ε ≤
        C * c ^ (2 / (1 + 2 * γ)) * (2 / (1 + 2 * γ)) ^ (1 / (1 + 2 * γ)) *
          ε ^ (-2 / (1 + 2 * γ)) * (Real.log ε⁻¹) ^ (1 / (1 + 2 * γ)) := by
  intro ε hε
  obtain ⟨hε0, hεb⟩ := hε
  have hεhalf : ε ≤ 1 / 2 := le_trans hεb (min_le_left _ _)
  have hεc : ε ≤ 1 / c := le_trans (le_trans hεb (min_le_right _ _)) (min_le_left _ _)
  have hεexp : ε ≤ c * Real.exp (-(1 + 2 * γ)) :=
    le_trans (le_trans hεb (min_le_right _ _)) (min_le_right _ _)
  obtain ⟨t, ht0, ht1, hL1, hbal⟩ := coin_sel_exists γ c hγ hc ε ⟨hε0, hεexp⟩
  exact coin_upper_bound_at hγ hC hc hcost_nn ht0 hL1 (hcost t ⟨ht0, ht1⟩)
    (herror t ⟨ht0, ht1⟩) hbal hε0 hεc hεhalf

end Qatlib.Papers.QIntegration00.MainResults.CoinMonteCarloUpper
