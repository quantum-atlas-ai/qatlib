/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StringRewrite07.MainResults.LineGraphSpectrum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete bounds for path spectral sums

The file bounds endpoint spectral weights using the stated sine-vector orthogonality identity
and controls every eigenvalue by `lineEigenvalue ℓ 0`. It gives a cubic lower bound on the first
endpoint weight and an upper bound on the absolute spectral power sum, then propagates the
latter through a `sqrt 2` scaling. See [JanzingWocjan2010].

## Main statements

* `lineWeight_zero_ge`: the first weight is at least `8 / (ℓ + 1) ^ 3`.
* `lineEigenvalue_abs_le_first`: the first eigenvalue bounds all spectral absolute values.
* `lineGraph_growth_bound`: the absolute weighted power sum is at most the first eigenvalue
  power under the orthogonality hypothesis.
* `delta_growth_of_entry`: the growth bound scales by a factor `sqrt 2` in the base.

## References

* [Janzing and Wocjan, 2010][JanzingWocjan2010]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StringRewrite07.MainResults

/-- If the coordinate columns of `e` have the stated orthonormality sums, then the sum of `|e j
a * e j b|` over `j` is at most one. See [JanzingWocjan2010]. -/
theorem sum_abs_weight_le_one {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (e : κ → ι → ℝ)
    (horth : ∀ a b : ι, ∑ j, e j a * e j b = if a = b then 1 else 0) (a b : ι) :
    ∑ j, |e j a * e j b| ≤ 1 := by
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ)
    (fun j => |e j a|) (fun j => |e j b|)
  have ha : (∑ j, |e j a| ^ 2) = 1 := by
    have h := horth a a
    rw [if_pos rfl] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    rw [sq_abs]; ring
  have hb : (∑ j, |e j b| ^ 2) = 1 := by
    have h := horth b b
    rw [if_pos rfl] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    rw [sq_abs]; ring
  have hsq : (∑ j, |e j a| * |e j b|) ^ 2 ≤ 1 := by
    rw [ha, hb, mul_one] at hcauchy
    exact hcauchy
  have hnn : 0 ≤ ∑ j, |e j a| * |e j b| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmain : ∑ j, |e j a| * |e j b| ≤ 1 := by nlinarith
  calc ∑ j, |e j a * e j b| = ∑ j, |e j a| * |e j b| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
    _ ≤ 1 := hmain

/-- If `0 ≤ x ≤ y ≤ π - x`, then `|cos y| ≤ cos x`. -/
theorem abs_cos_le_cos {x y : ℝ} (hx0 : 0 ≤ x)
    (hxy : x ≤ y) (hyle : y ≤ Real.pi - x) : |Real.cos y| ≤ Real.cos x := by
  have hpi := Real.pi_pos
  by_cases h : y ≤ Real.pi / 2
  · have hy0 : 0 ≤ Real.cos y :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h
    have hyle_pi : y ≤ Real.pi := by linarith
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hx0 hyle_pi hxy
    rw [abs_of_nonneg hy0]
    exact hmono
  · push Not at h
    have hy0 : 0 ≤ y := le_trans hx0 hxy
    have hnonpos : Real.cos y ≤ 0 := by
      have h1 : 0 ≤ Real.pi - y := by linarith
      have h2 : Real.pi - y ≤ Real.pi / 2 := by linarith
      have h3 : 0 ≤ Real.cos (Real.pi - y) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h2
      rw [Real.cos_pi_sub] at h3
      linarith
    have hyle_pi : Real.pi - y ≤ Real.pi := by linarith
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hx0 hyle_pi (by linarith : x ≤ Real.pi - y)
    rw [abs_of_nonpos hnonpos, ← Real.cos_pi_sub y]
    exact hmono

/-- The first path spectral value is nonnegative when `ℓ > 0`. -/
theorem lineEigenvalue_zero_nonneg {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 ≤ lineEigenvalue ℓ 0 := by
  unfold lineEigenvalue
  have hden : (0:ℝ) < (ℓ:ℝ) + 1 := by positivity
  have hx0 : 0 ≤ Real.pi / ((ℓ:ℝ) + 1) := by positivity
  have hxle : Real.pi / ((ℓ:ℝ) + 1) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hden]
    have h2 : (2:ℝ) ≤ (ℓ:ℝ) + 1 := by
      have h1 : (1:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hℓ
      linarith
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := Real.pi / ((ℓ:ℝ) + 1))
    (by linarith) hxle
  have harg : Real.pi * ((0:ℕ) + 1) / ((ℓ:ℝ) + 1) = Real.pi / ((ℓ:ℝ) + 1) := by
    push_cast
    ring
  rw [harg]
  nlinarith

/-- For `ℓ > 0` and `j < ℓ`, the absolute value of `lineEigenvalue ℓ j` is at most
`lineEigenvalue ℓ 0`. See [JanzingWocjan2010]. -/
theorem lineEigenvalue_abs_le_first {ℓ j : ℕ} (hℓ : 0 < ℓ) (hj : j < ℓ) :
    |lineEigenvalue ℓ j| ≤ lineEigenvalue ℓ 0 := by
  have hden : (0:ℝ) < (ℓ:ℝ) + 1 := by positivity
  set x : ℝ := Real.pi / ((ℓ:ℝ) + 1) with hxdef
  set y : ℝ := Real.pi * ((j:ℝ) + 1) / ((ℓ:ℝ) + 1) with hydef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxy : x ≤ y := by
    rw [hxdef, hydef]
    rw [div_le_div_iff_of_pos_right hden]
    have hj1 : (1:ℝ) ≤ (j:ℝ) + 1 := by
      have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    nlinarith [Real.pi_pos]
  have hyle : y ≤ Real.pi - x := by
    rw [hxdef, hydef, div_le_iff₀ hden]
    have hkey : (Real.pi - Real.pi / ((ℓ:ℝ) + 1)) * ((ℓ:ℝ) + 1)
        = Real.pi * ((ℓ:ℝ) + 1) - Real.pi := by
      field_simp
    rw [hkey]
    have hj2 : ((j:ℝ) + 1 + 1) ≤ (ℓ:ℝ) + 1 := by
      have hnat : (j + 1 + 1 : ℕ) ≤ ℓ + 1 := Nat.succ_le_succ (Nat.succ_le_of_lt hj)
      exact_mod_cast hnat
    nlinarith [Real.pi_pos]
  have hmain := abs_cos_le_cos hx0 hxy hyle
  unfold lineEigenvalue
  have hy_eq : Real.pi * ((j:ℝ) + 1) / ((ℓ:ℝ) + 1) = y := by rw [hydef]
  have hx_eq : Real.pi * ((0:ℕ) + 1) / ((ℓ:ℝ) + 1) = x := by
    rw [hxdef]; push_cast; ring
  rw [hy_eq, hx_eq]
  have habs : |(2:ℝ) * Real.cos y| = 2 * |Real.cos y| := by
    rw [abs_mul]; norm_num
  rw [habs]
  linarith

/-- The sine-form vector entry with spectral index zero and coordinate zero is `sqrt (2 / (ℓ +
1)) * sin (π / (ℓ + 1))`. -/
theorem lineEigvecEntry_zero_zero {ℓ : ℕ} :
    lineEigvecEntry ℓ 0 0 =
      Real.sqrt (2 / ((ℓ:ℝ) + 1)) * Real.sin (Real.pi / ((ℓ:ℝ) + 1)) := by
  unfold lineEigvecEntry
  have harg : Real.pi * ((0:ℕ) + 1) * ((0:ℕ) + 1) / ((ℓ:ℝ) + 1)
      = Real.pi / ((ℓ:ℝ) + 1) := by push_cast; ring
  rw [harg]

/-- For positive `ℓ`, the last coordinate of the spectral-index-zero sine vector equals `sqrt (2
/ (ℓ + 1)) * sin (π / (ℓ + 1))`. -/
theorem lineEigvecEntry_zero_last {ℓ : ℕ} (hℓ : 0 < ℓ) :
    lineEigvecEntry ℓ 0 (ℓ - 1) =
      Real.sqrt (2 / ((ℓ:ℝ) + 1)) * Real.sin (Real.pi / ((ℓ:ℝ) + 1)) := by
  unfold lineEigvecEntry
  rw [cast_pred_add_one hℓ]
  have harg : Real.pi * ((0:ℕ) + 1) * (ℓ:ℝ) / ((ℓ:ℝ) + 1)
      = Real.pi - Real.pi / ((ℓ:ℝ) + 1) := by
    have hden : ((ℓ:ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [harg, Real.sin_pi_sub]

/-- For positive `ℓ`, the first endpoint weight is `2 / (ℓ + 1) * sin² (π / (ℓ + 1))`. -/
theorem lineWeight_zero_eq {ℓ : ℕ} (hℓ : 0 < ℓ) :
    lineWeight ℓ 0 = 2 / ((ℓ:ℝ) + 1) * (Real.sin (Real.pi / ((ℓ:ℝ) + 1))) ^ 2 := by
  unfold lineWeight
  rw [lineEigvecEntry_zero_zero, lineEigvecEntry_zero_last hℓ]
  set s : ℝ := Real.sqrt (2 / ((ℓ:ℝ) + 1)) with hs
  set t : ℝ := Real.sin (Real.pi / ((ℓ:ℝ) + 1)) with ht
  have hsq : s * s = 2 / ((ℓ:ℝ) + 1) := by
    rw [hs]; exact Real.mul_self_sqrt (by positivity)
  calc s * t * (s * t) = (s * s) * (t * t) := by ring
    _ = 2 / ((ℓ:ℝ) + 1) * t ^ 2 := by rw [hsq]; ring

/-- For positive `ℓ`, the first endpoint weight is at least `(2 / (ℓ + 1)) ^ 3`. -/
theorem lineWeight_zero_ge_cube {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (2 / ((ℓ:ℝ) + 1)) ^ 3 ≤ lineWeight ℓ 0 := by
  rw [lineWeight_zero_eq hℓ]
  have hden : (0:ℝ) < (ℓ:ℝ) + 1 := by positivity
  have hx0 : 0 ≤ Real.pi / ((ℓ:ℝ) + 1) := by positivity
  have hxle : Real.pi / ((ℓ:ℝ) + 1) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hden]
    have h2 : (2:ℝ) ≤ (ℓ:ℝ) + 1 := by
      have h1 : (1:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hℓ
      linarith
    nlinarith [Real.pi_pos]
  have hsin_lb : 2 / ((ℓ:ℝ) + 1) ≤ Real.sin (Real.pi / ((ℓ:ℝ) + 1)) := by
    have h := Real.mul_le_sin hx0 hxle
    have hcancel : 2 / Real.pi * (Real.pi / ((ℓ:ℝ) + 1)) = 2 / ((ℓ:ℝ) + 1) := by
      field_simp
    rwa [hcancel] at h
  have hbase : 0 ≤ 2 / ((ℓ:ℝ) + 1) := by positivity
  have hsq2 : (2 / ((ℓ:ℝ) + 1)) ^ 2 ≤ (Real.sin (Real.pi / ((ℓ:ℝ) + 1))) ^ 2 :=
    pow_le_pow_left₀ hbase hsin_lb 2
  have hstep := mul_le_mul_of_nonneg_left hsq2 hbase
  have heq : 2 / ((ℓ:ℝ) + 1) * (2 / ((ℓ:ℝ) + 1)) ^ 2 = (2 / ((ℓ:ℝ) + 1)) ^ 3 := by ring
  rwa [heq] at hstep

/-- For positive `ℓ`, the first endpoint weight is at least `8 / (ℓ + 1) ^ 3`. See
[JanzingWocjan2010]. -/
theorem lineWeight_zero_ge {ℓ : ℕ} (hℓ : 0 < ℓ) :
    8 / ((ℓ:ℝ) + 1) ^ 3 ≤ lineWeight ℓ 0 := by
  have hle := lineWeight_zero_ge_cube hℓ
  have heq : (2 / ((ℓ:ℝ) + 1)) ^ 3 = 8 / ((ℓ:ℝ) + 1) ^ 3 := by
    field_simp
    ring
  rwa [heq] at hle

/-- The first endpoint weight is strictly positive when `ℓ > 0`. -/
theorem lineWeight_zero_pos {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 < lineWeight ℓ 0 := by
  have h := lineWeight_zero_ge hℓ
  have : (0:ℝ) < 8 / ((ℓ:ℝ) + 1) ^ 3 := by positivity
  linarith

/-- For positive `ℓ`, the stated orthogonality identity for the sine-vector entries implies that
the absolute endpoint spectral sum of `m`th powers is at most `(lineEigenvalue ℓ 0) ^ m`.
See [JanzingWocjan2010]. -/
theorem lineGraph_growth_bound {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ)
    (horth : ∀ a b : Fin ℓ,
      ∑ j : Fin ℓ, lineEigvecEntry ℓ (j:ℕ) (a:ℕ) * lineEigvecEntry ℓ (j:ℕ) (b:ℕ)
        = if a = b then 1 else 0) :
    |∑ j : Fin ℓ, (lineEigenvalue ℓ (j:ℕ)) ^ m * lineWeight ℓ (j:ℕ)|
      ≤ (lineEigenvalue ℓ 0) ^ m := by
  have hlam0 : 0 ≤ lineEigenvalue ℓ 0 := lineEigenvalue_zero_nonneg hℓ
  have hlam : ∀ j : Fin ℓ, |lineEigenvalue ℓ (j:ℕ)| ≤ lineEigenvalue ℓ 0 :=
    fun j => lineEigenvalue_abs_le_first hℓ j.isLt
  have hw : ∑ j : Fin ℓ, |lineWeight ℓ (j:ℕ)| ≤ 1 := by
    have h := sum_abs_weight_le_one (κ := Fin ℓ) (ι := Fin ℓ)
      (fun j k => lineEigvecEntry ℓ (j:ℕ) (k:ℕ)) horth
      ⟨0, hℓ⟩ ⟨ℓ - 1, Nat.sub_lt hℓ (by norm_num)⟩
    simpa only [lineWeight] using h
  exact spectral_sum_growth_bound (fun j : Fin ℓ => lineEigenvalue ℓ (j:ℕ))
    (fun j : Fin ℓ => lineWeight ℓ (j:ℕ)) hlam0 hlam hw m

/-- If `|P| ≤ lam0 ^ m`, `|k| ≤ 1`, and `Δ = k * (sqrt 2) ^ m * P`, then `|Δ| ≤ (sqrt 2 * lam0)
^ m`. -/
theorem delta_growth_of_entry {Δ k P : ℝ} {m : ℕ} {lam0 : ℝ}
    (hP : |P| ≤ lam0 ^ m) (hk : |k| ≤ 1)
    (hΔ : Δ = k * ((Real.sqrt 2) ^ m * P)) :
    |Δ| ≤ (Real.sqrt 2 * lam0) ^ m := by
  have hsqrt : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hp1 : |(Real.sqrt 2) ^ m| = (Real.sqrt 2) ^ m :=
    abs_of_nonneg (pow_nonneg hsqrt m)
  rw [hΔ, abs_mul, abs_mul, hp1]
  have hstep : |k| * ((Real.sqrt 2) ^ m * |P|) ≤ 1 * ((Real.sqrt 2) ^ m * lam0 ^ m) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
    exact mul_le_mul_of_nonneg_left hP (pow_nonneg hsqrt m)
  calc |k| * ((Real.sqrt 2) ^ m * |P|)
      ≤ 1 * ((Real.sqrt 2) ^ m * lam0 ^ m) := hstep
    _ = (Real.sqrt 2 * lam0) ^ m := by
        rw [one_mul, mul_pow]

end Qatlib.Papers.StringRewrite07.MainResults
