/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Norm Barrier for Dissipative Quadratic Differential Equations

This module formalizes Lemma 1 of Liu et al. on the scalar Riccati comparison
barrier for dissipative quadratic ODEs under the dissipation-to-nonlinearity
condition `R < 1`: root ordering `0 ≤ r₋ < x₀ < r₊`, monotonicity bounds on the
explicit barrier solution, and strict norm trapping `ρ(t) < x₀ < r₊` for `t > 0`.

## Main statements

* `lemma1_roots`: existence and ordering `0 ≤ r₋ < x0 < r₊` of the Riccati roots.
* `barrier_lt_initial` / `barrier_lt_rootPlus`: strict upper bounds on the explicit
  Riccati barrier for `t > 0`.
* `lemma1_norm_barrier`: differential-inequality comparison bound `ρ(t) < x0` and
  `ρ(t) < r₊` for all `t ∈ (0, T]`.

## References

* [Liu et al., 2021][LiuEtAl2021DissipNonlin], Section 4.1.1, Lemma 1, Eqs. (4.1)--(4.11).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier

open Set

/-- The smaller scalar root `r₋` of `a x² + b x + c = 0`. -/
def rootMinus (a b c : ℝ) : ℝ :=
  (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-- The larger scalar root `r₊` of `a x² + b x + c = 0`. -/
def rootPlus (a b c : ℝ) : ℝ :=
  (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-- The explicit Riccati comparison barrier solution starting at `x0`. -/
def barrier (a b c x0 t : ℝ) : ℝ :=
  (rootPlus a b c - rootMinus a b c) /
      (1 - Real.exp (a * (rootPlus a b c - rootMinus a b c) * t) *
        (1 - (rootPlus a b c - rootMinus a b c) / (x0 - rootMinus a b c)))
    + rootMinus a b c

/-- **Lemma 1 (roots)**: under `a > 0`, `b < 0`, `c ≥ 0`, `x0 > 0`, and
`a * x0 + c / x0 < -b`, the quadratic roots satisfy `0 ≤ r₋ < x0 < r₊`. -/
theorem lemma1_roots (a b c x0 : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) :
    rootMinus a b c < rootPlus a b c ∧ 0 ≤ rootMinus a b c ∧
      rootMinus a b c < x0 ∧ x0 < rootPlus a b c := by
  have hq : a * x0 ^ 2 + b * x0 + c < 0 := by
    have hmul : (a * x0 + c / x0) * x0 < (-b) * x0 :=
      mul_lt_mul_of_pos_right hR hx0
    have hx : (a * x0 + c / x0) * x0 = a * x0 ^ 2 + c := by
      field_simp
    rw [hx] at hmul
    nlinarith
  have hD : 0 < b ^ 2 - 4 * a * c := by
    by_contra h
    push Not at h
    have hid : 4 * a * (a * x0 ^ 2 + b * x0 + c)
        = (2 * a * x0 + b) ^ 2 - (b ^ 2 - 4 * a * c) := by ring
    nlinarith [sq_nonneg (2 * a * x0 + b)]
  have hsqrt : 0 < Real.sqrt (b ^ 2 - 4 * a * c) := Real.sqrt_pos.2 hD
  have hdiff : rootPlus a b c - rootMinus a b c
      = Real.sqrt (b ^ 2 - 4 * a * c) / a := by
    rw [rootPlus, rootMinus]
    field_simp
    ring
  have hrlt : rootMinus a b c < rootPlus a b c := by
    have : 0 < Real.sqrt (b ^ 2 - 4 * a * c) / a := div_pos hsqrt ha
    linarith
  have hDle : b ^ 2 - 4 * a * c ≤ b ^ 2 := by nlinarith [mul_nonneg (le_of_lt ha) hc]
  have hsq : Real.sqrt (b ^ 2 - 4 * a * c) ≤ Real.sqrt (b ^ 2) :=
    Real.sqrt_le_sqrt hDle
  have hbabs : Real.sqrt (b ^ 2) = -b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hb]
  have hnum : 0 ≤ -b - Real.sqrt (b ^ 2 - 4 * a * c) := by linarith
  have hrm : 0 ≤ rootMinus a b c := by
    have : 0 ≤ (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) :=
      div_nonneg hnum (by positivity)
    simpa [rootMinus] using this
  have hsum : rootMinus a b c + rootPlus a b c = -b / a := by
    rw [rootMinus, rootPlus]
    field_simp
    ring
  have hprod : rootMinus a b c * rootPlus a b c = c / a := by
    rw [rootMinus, rootPlus]
    field_simp
    nlinarith [Real.sq_sqrt (le_of_lt hD)]
  have hsuma : a * (rootMinus a b c + rootPlus a b c) = -b := by
    have h := hsum
    field_simp at h
    linarith
  have hproda : a * (rootMinus a b c * rootPlus a b c) = c := by
    have h := hprod
    field_simp at h
    linarith
  have hfac : a * (x0 - rootMinus a b c) * (x0 - rootPlus a b c)
      = a * x0 ^ 2 + b * x0 + c := by
    have hexp : (x0 - rootMinus a b c) * (x0 - rootPlus a b c)
        = x0 ^ 2 - (rootMinus a b c + rootPlus a b c) * x0
            + rootMinus a b c * rootPlus a b c := by ring
    nlinarith [hexp, hsuma, hproda]
  have hprodneg : (x0 - rootMinus a b c) * (x0 - rootPlus a b c) < 0 := by
    have : a * ((x0 - rootMinus a b c) * (x0 - rootPlus a b c)) < 0 := by
      nlinarith [hfac, hq]
    nlinarith [this, ha]
  have hleft : 0 < x0 - rootMinus a b c := by
    by_contra h
    push Not at h
    have hright0 : x0 - rootPlus a b c ≤ 0 := by linarith
    have hnn : 0 ≤ (x0 - rootMinus a b c) * (x0 - rootPlus a b c) :=
      mul_nonneg_of_nonpos_of_nonpos h hright0
    linarith
  have hright : x0 - rootPlus a b c < 0 := by
    by_contra h
    push Not at h
    have hnn : 0 ≤ (x0 - rootMinus a b c) * (x0 - rootPlus a b c) :=
      mul_nonneg (le_of_lt hleft) h
    linarith
  exact ⟨hrlt, hrm, by linarith, by linarith⟩

/-- The explicit barrier starts at `barrier a b c x0 0 = x0`. -/
theorem barrier_zero (a b c x0 : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) :
    barrier a b c x0 0 = x0 := by
  obtain ⟨hrlt, _, hrx, _⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hd : rootPlus a b c - rootMinus a b c ≠ 0 := by linarith
  have hy : x0 - rootMinus a b c ≠ 0 := by linarith
  simp only [barrier, Real.exp_zero, mul_zero]
  field_simp [hd, hy]
  ring

/-- **Lemma 1, Eq. (4.10)**: the explicit barrier is strictly below `x0` for all `t > 0`. -/
theorem barrier_lt_initial (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) (ht : 0 < t) :
    barrier a b c x0 t < x0 := by
  obtain ⟨hrlt, _, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  set rm := rootMinus a b c with hrmdef
  set rp := rootPlus a b c with hrpdef
  set d := rp - rm with hddef
  set y0 := x0 - rm with hy0def
  have hd : 0 < d := by rw [hddef]; linarith
  have hy0 : 0 < y0 := by rw [hy0def]; linarith
  have hk : 1 < d / y0 := by
    rw [hddef, hy0def, lt_div_iff₀ (by linarith)]
    linarith
  set E := Real.exp (a * d * t) with hEdef
  have hE : 1 < E := by
    rw [hEdef, Real.one_lt_exp_iff]
    have : 0 < a * d := mul_pos ha hd
    positivity
  set den := 1 - E * (1 - d / y0) with hdendef
  have hdenpos : 0 < den := by
    rw [hdendef]
    nlinarith [mul_pos (sub_pos.mpr hE) (sub_pos.mpr hk)]
  have hden_gt_k : d / y0 < den := by
    rw [hdendef]
    have : 0 < (E - 1) * (d / y0 - 1) := mul_pos (sub_pos.mpr hE) (sub_pos.mpr hk)
    nlinarith
  have hsub : barrier a b c x0 t - rm = d / den := by
    rw [barrier]
    rw [← hrmdef, ← hrpdef, ← hddef, ← hy0def]
    ring
  have hlt : d / den < y0 := by
    rw [div_lt_iff₀ hdenpos]
    have : d = y0 * (d / y0) := by field_simp
    have hdenk : y0 * (d / y0) < y0 * den := mul_lt_mul_of_pos_left hden_gt_k hy0
    linarith
  linarith [hsub, hlt, hy0def]

/-- **Lemma 1, Eq. (4.10)**: the explicit barrier is strictly below `r₊` for all `t > 0`. -/
theorem barrier_lt_rootPlus (a b c x0 t : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b) (ht : 0 < t) :
    barrier a b c x0 t < rootPlus a b c := by
  obtain ⟨hrlt, _, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  set rm := rootMinus a b c with hrmdef
  set rp := rootPlus a b c with hrpdef
  set d := rp - rm with hddef
  set y0 := x0 - rm with hy0def
  have hd : 0 < d := by rw [hddef]; linarith
  have hk : 1 < d / y0 := by
    rw [hddef, hy0def, lt_div_iff₀ (by linarith)]
    linarith
  set E := Real.exp (a * d * t) with hEdef
  have hE : 1 < E := by
    rw [hEdef, Real.one_lt_exp_iff]
    have : 0 < a * d := mul_pos ha hd
    positivity
  set den := 1 - E * (1 - d / y0) with hdendef
  have hdenpos : 0 < den := by
    rw [hdendef]
    nlinarith [mul_pos (sub_pos.mpr hE) (sub_pos.mpr hk)]
  have hden_gt_one : 1 < den := by
    rw [hdendef]
    nlinarith [mul_pos (sub_pos.mpr hE) (sub_pos.mpr hk)]
  have hsub : barrier a b c x0 t - rm = d / den := by
    rw [barrier]
    rw [← hrmdef, ← hrpdef, ← hddef, ← hy0def]
    ring
  have hlt : d / den < d := by
    rw [div_lt_iff₀ hdenpos]
    nlinarith [hd, hden_gt_one]
  linarith [hsub, hlt, hddef]

private lemma quadratic_neg_between_roots (a b c y : ℝ) (ha : 0 < a)
    (hmy : rootMinus a b c < y) (hyp : y < rootPlus a b c) :
    a * y ^ 2 + b * y + c < 0 := by
  have hD : 0 ≤ b ^ 2 - 4 * a * c := by
    by_contra! h
    have heq : rootMinus a b c = rootPlus a b c := by
      simp [rootMinus, rootPlus, Real.sqrt_eq_zero_of_nonpos h.le]
    linarith
  have hfac : a * y ^ 2 + b * y + c =
      a * (y - rootMinus a b c) * (y - rootPlus a b c) := by
    unfold rootMinus rootPlus
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ b ^ 2 - a * c * 4 by nlinarith [hD])]
  rw [hfac]
  exact mul_neg_of_pos_of_neg (mul_pos ha (sub_pos.mpr hmy)) (sub_neg.mpr hyp)

/-- **Lemma 1 (norm barrier)**: if `ρ` is continuous and nonnegative on `[0, T]`,
starts at `ρ 0 = x0`, and satisfies the right-hand differential inequality
`ρ' t ≤ a * ρ t ^ 2 + b * ρ t + c` on `[0, T)`, then `ρ t < x0` and
`ρ t < rootPlus a b c` for every `t ∈ (0, T]`. -/
theorem lemma1_norm_barrier (a b c x0 T : ℝ) (ha : 0 < a) (hb : b < 0) (hc : 0 ≤ c)
    (hx0 : 0 < x0) (hR : a * x0 + c / x0 < -b)
    (ρ ρ' : ℝ → ℝ) (hcont : ContinuousOn ρ (Icc 0 T)) (hρ0 : ρ 0 = x0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt ρ (ρ' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, ρ' t ≤ a * ρ t ^ 2 + b * ρ t + c)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ ρ t) :
    ∀ t ∈ Icc 0 T, 0 < t → ρ t < x0 ∧ ρ t < rootPlus a b c := by
  refine fun t htmem htpos => (And.left ⟨?_, hnonneg⟩)
  obtain ⟨_, _, hrx, hxr⟩ := lemma1_roots a b c x0 ha hb hc hx0 hR
  have hT : 0 < T := htpos.trans_le htmem.2
  have hneg : ρ' 0 < 0 := lt_of_le_of_lt (hbound 0 ⟨le_rfl, hT⟩) (by
    simpa only [hρ0] using quadratic_neg_between_roots a b c x0 ha hrx hxr)
  obtain ⟨t₀, ht₀, hdrop⟩ : ∃ t₀ ∈ Ioo 0 t, ρ t₀ < x0 := by
    by_contra! h
    have hlim := (hasDerivWithinAt_iff_tendsto_slope'
      (show (0 : ℝ) ∉ Ioi 0 from lt_irrefl (0 : ℝ))).mp
      (hderiv 0 ⟨le_rfl, hT⟩).Ioi_of_Ici
    have hnonneg' : 0 ≤ ρ' 0 := ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsGT htpos] with s hs
      rw [slope_def_field, hρ0, sub_zero]
      exact div_nonneg (sub_nonneg.mpr (h s hs)) hs.1.le)
    exact (not_lt_of_ge hnonneg') hneg
  set y := (max (rootMinus a b c) (ρ t₀) + x0) / 2
  have hmax : max (rootMinus a b c) (ρ t₀) < x0 := max_lt hrx hdrop
  have hmy : rootMinus a b c < y := by
    dsimp [y]; linarith [le_max_left (rootMinus a b c) (ρ t₀)]
  have hρy : ρ t₀ < y := by
    dsimp [y]; linarith [le_max_right (rootMinus a b c) (ρ t₀)]
  have hyx : y < x0 := by dsimp [y]; linarith
  have hqy := quadratic_neg_between_roots a b c y ha hmy (hyx.trans hxr)
  have hsub : Ico t₀ t ⊆ Ico 0 T := fun s hs =>
    ⟨ht₀.1.le.trans hs.1, hs.2.trans_le htmem.2⟩
  have hfence := image_le_of_deriv_right_lt_deriv_boundary
    (hcont.mono (Icc_subset_Icc ht₀.1.le htmem.2))
    (fun s hs => hderiv s (hsub hs)) (B := fun _ : ℝ => y) (B' := fun _ : ℝ => 0)
    hρy.le (fun s => hasDerivAt_const s y) (by
      intro s hs heq
      have h := hbound s (hsub hs)
      rw [heq] at h
      exact h.trans_lt hqy)
  have hfinal : ρ t < x0 := (hfence ⟨ht₀.2.le, le_rfl⟩).trans_lt hyx
  exact ⟨hfinal, hfinal.trans hxr⟩

end Qatlib.Papers.DissipNonlin20.MainResults.NormBarrier
