/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearSolver24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver24 — the Chebyshev filter polynomials (Lemma 1 and Lemma 3)

Fixed source: arXiv:2406.12086, Appendix B.2.
* Lemma 1, p. 19, with the degree choice Eq. (51) and the polynomial of
  Eq. (52): `F_{Δ,ℓ}(x) = T_ℓ((1+Δ²-2x²)/(1-Δ²)) / T_ℓ((1+Δ²)/(1-Δ²))`.
* Lemma 3, p. 21, with the reflection polynomial of Eq. (62):
  `K_{Δ,ℓ}(x) = (2T_ℓ(z(x)) - D + 1)/(D + 1)`, `D = T_ℓ((1+Δ²)/(1-Δ²))`.

Both lemmas are proved here from Mathlib's Chebyshev API
(`Polynomial.Chebyshev.T_real_cos`, `T_real_cosh`) and the monotonicity of
`cosh`/`arcosh`; no algorithmic modelling is involved in this module.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.FilterPolynomials

open Polynomial
open Qatlib.Papers.QLinearSolver24.MainResults

/-- The paper's condition `0 < Δ < 1` makes the filter argument
`(1 + Δ²)/(1 - Δ²)` at least one. -/
theorem one_le_filterArg_zero {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    1 ≤ (1 + Δ ^ 2) / (1 - Δ ^ 2) := by
  rw [le_div_iff₀ (by nlinarith [sq_nonneg Δ])]
  nlinarith [sq_nonneg Δ]

/-- The filter denominator is a `cosh`, hence at least one. -/
theorem filterDenom_eq_cosh {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ) :
    filterDenom Δ ℓ =
      Real.cosh ((ℓ : ℝ) * Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2))) := by
  unfold filterDenom chebT
  conv_lhs => rw [← Real.cosh_arcosh (one_le_filterArg_zero hΔ0 hΔ1)]
  simp only [Polynomial.Chebyshev.T_real_cosh]
  rw [show ((ℓ : ℤ) : ℝ) = (ℓ : ℝ) from by push_cast; rfl]

/-- The `filterDenom_pos` result for the QLinearSolver24 paper model. -/
theorem filterDenom_pos {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ) :
    0 < filterDenom Δ ℓ := by
  rw [filterDenom_eq_cosh hΔ0 hΔ1]
  exact lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)

/-- The `one_le_filterDenom` result for the QLinearSolver24 paper model. -/
theorem one_le_filterDenom {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ) :
    1 ≤ filterDenom Δ ℓ := by
  rw [filterDenom_eq_cosh hΔ0 hΔ1]
  exact Real.one_le_cosh _

/-- `T_ℓ` is bounded by one on the unit interval (paper Eq. (53) first branch,
p. 19). -/
theorem chebT_abs_le_one {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |chebT n x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos h1 h2
  rw [chebT, ← hcos, Polynomial.Chebyshev.T_real_cos]
  exact abs_le.mpr (Real.cos_mem_Icc _)

/-- On `[1, ∞)`, `T_ℓ` is monotonically increasing: `cosh(ℓ·arcosh z)` is
increasing in `z` (paper Eq. (53) second branch). -/
theorem chebT_mono {n : ℕ} {z c : ℝ} (hz : 1 ≤ z) (hzc : z ≤ c) :
    chebT n z ≤ chebT n c := by
  have hc : 1 ≤ c := hz.trans hzc
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  unfold chebT
  rw [show z = Real.cosh (Real.arcosh z) from (Real.cosh_arcosh hz).symm,
    show c = Real.cosh (Real.arcosh c) from (Real.cosh_arcosh hc).symm]
  simp only [Polynomial.Chebyshev.T_real_cosh]
  rw [Real.cosh_le_cosh]
  rw [abs_of_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le n)
      (Real.arcosh_nonneg hz)),
    abs_of_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le n)
      (Real.arcosh_nonneg hc))]
  have hstep : Real.arcosh z ≤ Real.arcosh c :=
    (Real.arcosh_le_arcosh hzpos hcpos).mpr hzc
  push_cast
  exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg n)

/-- `T_ℓ` on `[-1, D]` is bounded in absolute value by `D` whenever `D` is a
value of `T_ℓ` at an argument at least one and `D ≥ 1`.  This is the bound
used in Lemma 1 property 1 (p. 19). -/
theorem chebT_abs_le_of_mem_Icc {n : ℕ} {z c : ℝ}
    (_hc : 1 ≤ c) (hz1 : -1 ≤ z) (hzc : z ≤ c)
    (hD1 : 1 ≤ chebT n c) : |chebT n z| ≤ chebT n c := by
  rcases le_or_gt z 1 with hz | hz
  · have h1 : |chebT n z| ≤ 1 := chebT_abs_le_one ⟨hz1, hz⟩
    exact h1.trans hD1
  · have hzpos : 0 < z := lt_trans zero_lt_one hz
    have hle : chebT n z ≤ chebT n c := chebT_mono (le_of_lt hz) hzc
    have hge1 : 1 ≤ chebT n z := by
      rw [chebT, show z = Real.cosh (Real.arcosh z) from
        (Real.cosh_arcosh (le_of_lt hz)).symm]
      simp
    rw [abs_of_nonneg (le_trans zero_le_one hge1)]
    exact hle

/-- Membership of the filter argument in `[-1, D]` for `x ∈ [-1, 1]`. -/
theorem filterArg_mem_unit {Δ x : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    filterArg Δ x ∈ Set.Icc (-1 : ℝ) ((1 + Δ ^ 2) / (1 - Δ ^ 2)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hden : (0 : ℝ) < 1 - Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have hx2le : x ^ 2 ≤ 1 := by
    have := mul_nonneg (show (0:ℝ) ≤ 1 - x by linarith)
      (show (0:ℝ) ≤ 1 + x by linarith)
    nlinarith [this]
  constructor
  · unfold filterArg
    rw [le_div_iff₀ hden]
    nlinarith [hx2le]
  · unfold filterArg
    rw [div_le_div_iff_of_pos_right hden]
    nlinarith [sq_nonneg x]

/-- Membership of the filter argument in `[-1, 1]` for `x ∈ [Δ, 1]`. -/
theorem filterArg_mem_delta {Δ x : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hx : x ∈ Set.Icc Δ 1) :
    filterArg Δ x ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨hxΔ, hx1⟩ := hx
  have hden : (0 : ℝ) < 1 - Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have hxsq : Δ ^ 2 ≤ x ^ 2 := by
    have h := mul_self_le_mul_self (le_of_lt hΔ0) hxΔ
    nlinarith [h]
  have hx2le : x ^ 2 ≤ 1 := by
    have := mul_nonneg (show (0:ℝ) ≤ 1 - x by linarith)
      (show (0:ℝ) ≤ 1 + x by linarith)
    nlinarith [this]
  constructor
  · unfold filterArg
    rw [le_div_iff₀ hden]
    nlinarith [hx2le]
  · unfold filterArg
    rw [div_le_one hden]
    nlinarith [hxsq]

/-- `F_{Δ,ℓ}(0) = 1` — Lemma 1 property 3 (p. 19). -/
theorem F_at_zero {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ) :
    F Δ ℓ 0 = 1 := by
  have hden := filterDenom_pos hΔ0 hΔ1 ℓ
  unfold F
  have harg : filterArg Δ 0 = (1 + Δ ^ 2) / (1 - Δ ^ 2) := by
    unfold filterArg; ring_nf
  rw [harg]
  exact div_self (ne_of_gt hden)

/-- **Lemma 1** (p. 19, Eq. (52)–(53)): the kernel-projection filter
`F_{Δ,ℓ}` is bounded by `1` on `[-1,1]`, is at most `1/T_ℓ((1+Δ²)/(1-Δ²))`
(and hence at most `η`) on `[Δ,1]`, and maps `0` to `1`.  The accuracy
condition is the paper's `ℓ ≥ arccosh(η⁻¹)/arccosh((1+Δ²)/(1-Δ²))`
(Eq. (51)). -/
theorem lemma1_F_bounds (Δ η : ℝ) (ℓ : ℕ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hell : Real.arcosh η⁻¹ ≤
      (ℓ : ℝ) * Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2))) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |F Δ ℓ x| ≤ 1) ∧
      (∀ x ∈ Set.Icc Δ 1, |F Δ ℓ x| ≤ (filterDenom Δ ℓ)⁻¹ ∧ |F Δ ℓ x| ≤ η) ∧
      F Δ ℓ 0 = 1 := by
  have hden := filterDenom_pos hΔ0 hΔ1 ℓ
  have hden1 := one_le_filterDenom hΔ0 hΔ1 ℓ
  have hc := one_le_filterArg_zero hΔ0 hΔ1
  -- the accuracy bound `η⁻¹ ≤ D`
  have hDcosh := filterDenom_eq_cosh hΔ0 hΔ1 ℓ
  have hDinv : η⁻¹ ≤ filterDenom Δ ℓ := by
    rw [hDcosh]
    have hηinv : (1 : ℝ) ≤ η⁻¹ := (one_le_inv₀ hη0).mpr hη1
    have hcosh_step : Real.cosh (Real.arcosh η⁻¹) ≤
        Real.cosh ((ℓ : ℝ) * Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2))) := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg (Real.arcosh_nonneg hηinv),
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg ℓ) (Real.arcosh_nonneg hc))]
      exact hell
    simpa [Real.cosh_arcosh hηinv] using hcosh_step
  refine ⟨?_, ?_, F_at_zero hΔ0 hΔ1 ℓ⟩
  · intro x hx
    have hzmem := filterArg_mem_unit hΔ0 hΔ1 hx
    have hT := chebT_abs_le_of_mem_Icc hc hzmem.1 hzmem.2 hden1
    unfold F
    rw [abs_div, abs_of_pos hden]
    exact (div_le_one hden).mpr hT
  · intro x hx
    have hzmem := filterArg_mem_delta hΔ0 hΔ1 hx
    have hT := chebT_abs_le_one (n := ℓ) hzmem
    have hFle : |F Δ ℓ x| ≤ (filterDenom Δ ℓ)⁻¹ := by
      unfold F
      rw [abs_div, abs_of_pos hden, div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_right hT (le_of_lt (inv_pos.mpr hden))
    refine ⟨hFle, ?_⟩
    -- `1/D ≤ η` from `η⁻¹ ≤ D`
    have hDle : 1 ≤ η * filterDenom Δ ℓ := by
      have := mul_le_mul_of_nonneg_left hDinv (le_of_lt hη0)
      simpa [mul_inv_cancel₀ (ne_of_gt hη0)] using this
    calc |F Δ ℓ x| ≤ (filterDenom Δ ℓ)⁻¹ := hFle
      _ ≤ η := by
        simpa [one_div] using (div_le_iff₀ hden).mpr hDle

/-- `K_{Δ,ℓ}(0) = 1` — Lemma 3 property 3 (p. 21). -/
theorem K_at_zero {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ) :
    K Δ ℓ 0 = 1 := by
  have hden := filterDenom_pos hΔ0 hΔ1 ℓ
  have harg : filterArg Δ 0 = (1 + Δ ^ 2) / (1 - Δ ^ 2) := by
    unfold filterArg; ring_nf
  unfold K filterDenom at *
  rw [harg]
  have hne : chebT ℓ ((1 + Δ ^ 2) / (1 - Δ ^ 2)) + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The reflection polynomial on `[-1,1]`: writing `D = T_ℓ((1+Δ²)/(1-Δ²))`
and `T = T_ℓ(z(x))`, `K + 1 = 2(T+1)/(D+1)`, and `T ∈ [-1, D]`. -/
theorem K_abs_le_one {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ℓ : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |K Δ ℓ x| ≤ 1 := by
  have hden := filterDenom_pos hΔ0 hΔ1 ℓ
  have hden1 := one_le_filterDenom hΔ0 hΔ1 ℓ
  have hc := one_le_filterArg_zero hΔ0 hΔ1
  have hzmem := filterArg_mem_unit hΔ0 hΔ1 hx
  have hTupper := chebT_abs_le_of_mem_Icc hc hzmem.1 hzmem.2 hden1
  have hTlower : -1 ≤ chebT ℓ (filterArg Δ x) := by
    rcases le_or_gt (filterArg Δ x) 1 with hz | hz
    · exact (abs_le.mp (chebT_abs_le_one ⟨hzmem.1, hz⟩)).1
    · have hpos : 0 < filterArg Δ x := lt_trans zero_lt_one hz
      rw [chebT, show filterArg Δ x = Real.cosh (Real.arcosh (filterArg Δ x)) from
        (Real.cosh_arcosh (le_of_lt hz)).symm]
      simp only [Polynomial.Chebyshev.T_real_cosh]
      push_cast
      linarith [Real.one_le_cosh ((ℓ : ℝ) * Real.arcosh (filterArg Δ x))]
  unfold K
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < filterDenom Δ ℓ + 1)]
  rw [div_le_one (by linarith : (0:ℝ) < filterDenom Δ ℓ + 1)]
  have hTle : chebT ℓ (filterArg Δ x) ≤ filterDenom Δ ℓ := by
    simpa [filterDenom] using (abs_le.mp hTupper).2
  rw [abs_le]
  constructor
  · nlinarith [hTlower]
  · nlinarith [hTle]

/-- **Lemma 3** (p. 21, Eq. (62)): the kernel-reflection polynomial.
On `[-1,1]` it is bounded by `1`; on `[Δ,1]` it lies in
`[-1, -1 + 4/(T_ℓ((1+Δ²)/(1-Δ²)) + 1)]`, equivalently
`0 ≤ K + 1 ≤ 4/(D+1)`, which the paper uses through
`δ₁′ = K + 1 ∈ [0, 4η/(1+η)]` (Eq. (66)); and `K(0) = 1`.

The printed Lemma 3 displays `|K_{Δ,ℓ}(x)| ≤ -1 + 4/(T_ℓ(·)+1)`; that
absolute-value sign is a typographical error in the source: Eq. (66) and the
proof only assert the negative-side bound `K ≥ -1` with `K + 1 ≤ 4/(D+1)`,
which is the statement formalised here. -/
theorem lemma3_K_bounds (Δ η : ℝ) (ℓ : ℕ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hell : Real.arcosh η⁻¹ ≤
      (ℓ : ℝ) * Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2))) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |K Δ ℓ x| ≤ 1) ∧
      (∀ x ∈ Set.Icc Δ 1,
        0 ≤ K Δ ℓ x + 1 ∧ K Δ ℓ x + 1 ≤ 4 / (filterDenom Δ ℓ + 1) ∧
          K Δ ℓ x + 1 ≤ 4 * η / (1 + η)) ∧
      K Δ ℓ 0 = 1 := by
  have hden := filterDenom_pos hΔ0 hΔ1 ℓ
  have hc := one_le_filterArg_zero hΔ0 hΔ1
  have hDinv : η⁻¹ ≤ filterDenom Δ ℓ := by
    rw [filterDenom_eq_cosh hΔ0 hΔ1 ℓ]
    have hηinv : (1 : ℝ) ≤ η⁻¹ := (one_le_inv₀ hη0).mpr hη1
    have hcosh_step : Real.cosh (Real.arcosh η⁻¹) ≤
        Real.cosh ((ℓ : ℝ) * Real.arcosh ((1 + Δ ^ 2) / (1 - Δ ^ 2))) := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg (Real.arcosh_nonneg hηinv),
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg ℓ) (Real.arcosh_nonneg hc))]
      exact hell
    simpa [Real.cosh_arcosh hηinv] using hcosh_step
  refine ⟨?_, ?_, K_at_zero hΔ0 hΔ1 ℓ⟩
  · intro x hx
    exact K_abs_le_one hΔ0 hΔ1 ℓ hx
  · intro x hx
    have hzmem := filterArg_mem_delta hΔ0 hΔ1 hx
    have hTabs := chebT_abs_le_one (n := ℓ) hzmem
    have hT1 : chebT ℓ (filterArg Δ x) ≤ 1 := (abs_le.mp hTabs).2
    have hT2 : -1 ≤ chebT ℓ (filterArg Δ x) := (abs_le.mp hTabs).1
    have hpos : (0:ℝ) < filterDenom Δ ℓ + 1 := by linarith
    have hK : K Δ ℓ x + 1 =
        2 * (chebT ℓ (filterArg Δ x) + 1) / (filterDenom Δ ℓ + 1) := by
      unfold K
      field_simp
      ring
    rw [hK]
    constructor
    · apply div_nonneg
      · nlinarith [hT2]
      · linarith
    constructor
    · rw [div_le_div_iff_of_pos_right hpos]
      nlinarith [hT1]
    · -- `4/(D+1) ≤ 4η/(1+η)` from `η⁻¹ ≤ D`
      have hDle : 1 ≤ η * filterDenom Δ ℓ := by
        have := mul_le_mul_of_nonneg_left hDinv (le_of_lt hη0)
        simpa [mul_inv_cancel₀ (ne_of_gt hη0)] using this
      rw [div_le_div_iff₀ hpos (by linarith : (0:ℝ) < 1 + η)]
      nlinarith [hDle, hT1, hη0]

end Qatlib.Papers.QLinearSolver24.MainResults.FilterPolynomials
