/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Lemma 8 step and error parameter bounds

This module chooses the integer step count `lemma8Steps` and parameter `lemma8Eps`, then bounds
the latter, under the stated parameter hypotheses, between `δ / (2 * (Λ * t))` and `δ / (Λ *
t)`. The result `lemma8_improved_simulation` packages the existence of a parameter satisfying
these bounds, its range conditions, and the scalar cost estimate derived by
`lemma8_query_bound`.

These arithmetic estimates accompany the improved simulation analysis of Lemma 8 in
[BerryChilds2012].

## Main statements

* `lemma8_eps_ge_half` gives a lower bound on the selected parameter.
* `lemma8_improved_simulation` collects parameter existence and scalar cost bounds.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

/-- The natural ceiling of `Λ1 * Λ * t ^ 2 / δ`, used as the step count for Lemma 8. -/
def lemma8Steps (Λ1 Λ t δ : ℝ) : ℕ := ⌈Λ1 * Λ * t ^ 2 / δ⌉₊

/-- The parameter `Λ1 * t / lemma8Steps Λ1 Λ t δ` associated with the selected integer step
count. -/
def lemma8Eps (Λ1 Λ t δ : ℝ) : ℝ := Λ1 * t / (lemma8Steps Λ1 Λ t δ : ℝ)

/-- For positive `δ`, `t`, and `Λ`, the conditions `sqrt δ ≤ Λ * t` and `Λ ≤ Λ1` imply that `Λ1
* Λ * t ^ 2 / δ` is at least one. -/
theorem lemma8_ratio_ge_one {Λ Λ1 t δ : ℝ} (hδ0 : 0 < δ) (ht : 0 < t) (hΛ0 : 0 < Λ)
    (hcond1 : Real.sqrt δ ≤ Λ * t) (hcond3 : Λ ≤ Λ1) :
    1 ≤ Λ1 * Λ * t ^ 2 / δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have h1 : 1 ≤ Λ * t / Real.sqrt δ := by
    rw [le_div_iff₀ hs]
    linarith
  have h2 : 1 ≤ Λ1 * t / Real.sqrt δ := by
    rw [le_div_iff₀ hs]
    have hle : Λ * t ≤ Λ1 * t := by gcongr
    linarith
  have hprod : 1 ≤ (Λ1 * t / Real.sqrt δ) * (Λ * t / Real.sqrt δ) := by
    simpa using! mul_le_mul h2 h1 (by norm_num : (0 : ℝ) ≤ 1) (le_trans (by norm_num) h2)
  have heq : (Λ1 * t / Real.sqrt δ) * (Λ * t / Real.sqrt δ) = Λ1 * Λ * t ^ 2 / δ := by
    field_simp
    rw [Real.sq_sqrt hδ0.le]
  linarith [hprod, heq]

/-- The selected step count is at least the real ratio `Λ1 * Λ * t ^ 2 / δ`. -/
theorem lemma8_ratio_le_steps (Λ1 Λ t δ : ℝ) :
    Λ1 * Λ * t ^ 2 / δ ≤ (lemma8Steps Λ1 Λ t δ : ℝ) :=
  Nat.le_ceil _

/-- When the defining ratio is positive, its natural ceiling is strictly less than that ratio
plus one. -/
theorem lemma8_steps_lt_add_one {Λ1 Λ t δ : ℝ} (hratio : 0 < Λ1 * Λ * t ^ 2 / δ) :
    (lemma8Steps Λ1 Λ t δ : ℝ) < Λ1 * Λ * t ^ 2 / δ + 1 :=
  Nat.ceil_lt_add_one (le_of_lt hratio)

/-- The selected parameter `lemma8Eps` is positive when `δ`, `t`, `Λ`, and `Λ1` are positive. -/
theorem lemma8_eps_pos {Λ Λ1 t δ : ℝ} (hδ0 : 0 < δ) (ht : 0 < t) (hΛ0 : 0 < Λ)
    (hΛ1 : 0 < Λ1) : 0 < lemma8Eps Λ1 Λ t δ := by
  have hratio0 : 0 < Λ1 * Λ * t ^ 2 / δ := by positivity
  have hK : 0 < (lemma8Steps Λ1 Λ t δ : ℝ) := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hratio0)
  unfold lemma8Eps
  exact div_pos (mul_pos hΛ1 ht) hK

/-- For positive parameters, `lemma8Eps` is at most `δ / (Λ * t)`. See [Berry and Childs, Lemma
8][BerryChilds2012]. -/
theorem lemma8_eps_le_delta {Λ Λ1 t δ : ℝ} (hδ0 : 0 < δ) (ht : 0 < t) (hΛ0 : 0 < Λ)
    (hΛ1 : 0 < Λ1) : lemma8Eps Λ1 Λ t δ ≤ δ / (Λ * t) := by
  have hratio0 : 0 < Λ1 * Λ * t ^ 2 / δ := by positivity
  have hK : 0 < (lemma8Steps Λ1 Λ t δ : ℝ) := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hratio0)
  have hΛt : 0 < Λ * t := mul_pos hΛ0 ht
  have hKge := lemma8_ratio_le_steps Λ1 Λ t δ
  have hmul : Λ1 * Λ * t ^ 2 ≤ δ * (lemma8Steps Λ1 Λ t δ : ℝ) := by
    rw [div_le_iff₀ hδ0] at hKge
    linarith
  unfold lemma8Eps
  rw [div_le_div_iff₀ hK hΛt]
  have hsq : Λ1 * t * (Λ * t) = Λ1 * Λ * t ^ 2 := by ring
  linarith

/-- For positive parameters and a defining ratio at least one, `lemma8Eps` is at least `δ / (2 *
(Λ * t))`. See [Berry and Childs, Lemma 8][BerryChilds2012]. -/
theorem lemma8_eps_ge_half {Λ Λ1 t δ : ℝ} (hδ0 : 0 < δ) (ht : 0 < t) (hΛ0 : 0 < Λ)
    (hΛ1 : 0 < Λ1) (hratio : 1 ≤ Λ1 * Λ * t ^ 2 / δ) :
    δ / (2 * (Λ * t)) ≤ lemma8Eps Λ1 Λ t δ := by
  have hratio0 : 0 < Λ1 * Λ * t ^ 2 / δ := lt_of_lt_of_le zero_lt_one hratio
  have hK : 0 < (lemma8Steps Λ1 Λ t δ : ℝ) := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hratio0)
  have hKlt := lemma8_steps_lt_add_one (Λ1 := Λ1) (Λ := Λ) (t := t) (δ := δ) hratio0
  have hKle : (lemma8Steps Λ1 Λ t δ : ℝ) ≤ 2 * (Λ1 * Λ * t ^ 2 / δ) := by linarith
  have hΛt : 0 < Λ * t := mul_pos hΛ0 ht
  have hmul : δ * (lemma8Steps Λ1 Λ t δ : ℝ) ≤ 2 * (Λ1 * Λ * t ^ 2) := by
    have := mul_le_mul_of_nonneg_left hKle (le_of_lt hδ0)
    have heq : δ * (2 * (Λ1 * Λ * t ^ 2 / δ)) = 2 * (Λ1 * Λ * t ^ 2) := by
      field_simp
    linarith
  unfold lemma8Eps
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * (Λ * t)) hK]
  have hrhs : Λ1 * t * (2 * (Λ * t)) = 2 * (Λ1 * Λ * t ^ 2) := by ring
  linarith

/-- For positive parameters, `δ ≤ 1` and `sqrt δ ≤ Λ * t` ensure that `lemma8Eps ≤ 1`. -/
theorem lemma8_eps_le_one {Λ Λ1 t δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 < t)
    (hΛ0 : 0 < Λ) (hΛ1 : 0 < Λ1) (hcond1 : Real.sqrt δ ≤ Λ * t) :
    lemma8Eps Λ1 Λ t δ ≤ 1 := by
  have hε := lemma8_eps_le_delta (Λ := Λ) (Λ1 := Λ1) (t := t) (δ := δ) hδ0 ht hΛ0 hΛ1
  have hs1 : Real.sqrt δ ≤ 1 := by
    have := Real.sqrt_le_sqrt hδ1
    simpa using! this
  have hδle : δ ≤ Real.sqrt δ := by
    have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
    nlinarith [Real.sqrt_nonneg δ, hs1]
  have hδt : δ ≤ Λ * t := le_trans hδle hcond1
  have hdiv : δ / (Λ * t) ≤ 1 := by
    rw [div_le_one (mul_pos hΛ0 ht)]
    exact hδt
  linarith

/-- For positive `ε` and `Λ1` and nonnegative `Λmax`, rewrite the product of the real step
factor and square root amplification factor as `t * sqrt (Λ1 * Λmax * D / ε)`. See [Berry
and Childs, Lemma 8][BerryChilds2012]. -/
theorem lemma8_query_identity {Λ1 Λmax ε t : ℝ} {D : ℕ} (hε0 : 0 < ε) (hΛ1 : 0 < Λ1)
    (hmax0 : 0 ≤ Λmax) :
    (Λ1 * t / ε) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) =
      t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε) := by
  have hx : 0 ≤ ε * Λmax * (D : ℝ) / Λ1 := by positivity
  have hΛ1e : 0 ≤ Λ1 / ε := le_of_lt (div_pos hΛ1 hε0)
  calc (Λ1 * t / ε) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)
      = t * ((Λ1 / ε) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)) := by ring
    _ = t * (Real.sqrt ((Λ1 / ε) ^ 2) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1)) := by
          rw [Real.sqrt_sq hΛ1e]
    _ = t * Real.sqrt ((Λ1 / ε) ^ 2 * (ε * Λmax * (D : ℝ) / Λ1)) := by
          rw [Real.sqrt_mul (sq_nonneg (Λ1 / ε))]
    _ = t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε) := by
          congr 2
          field_simp

/-- For the stated positive parameters and nonnegative `Λmax`, rewrite `lemma8QueryExpr` as `t *
sqrt (Λmax * D * Λ1 * Λ * t / δ)`. See [Berry and Childs, Lemma 8][BerryChilds2012]. -/
theorem lemma8QueryExpr_eq {Λ Λ1 Λmax t δ : ℝ} {D : ℕ}
    (hΛ : 0 < Λ) (hΛ1 : 0 < Λ1) (hD : 0 < D) (ht : 0 < t) (hδ : 0 < δ)
    (hmax0 : 0 ≤ Λmax) :
    lemma8QueryExpr Λ Λ1 Λmax D t δ =
      t * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ * t / δ) := by
  unfold lemma8QueryExpr
  rw [Real.rpow_eq_pow t (3 / 2)]
  have hpow : t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
    rw [Real.rpow_div_two_eq_sqrt (x := t) (r := 3) ht.le]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    calc Real.sqrt t ^ 3 = Real.sqrt t ^ 2 * Real.sqrt t := by ring
      _ = t * Real.sqrt t := by rw [hsq]
  rw [hpow]
  have hc : 0 ≤ Λmax * (D : ℝ) * Λ1 * Λ / δ := by positivity
  calc t * Real.sqrt t * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ / δ)
      = t * (Real.sqrt t * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ / δ)) := by ring
    _ = t * Real.sqrt (t * (Λmax * (D : ℝ) * Λ1 * Λ / δ)) := by
          rw [Real.sqrt_mul ht.le]
    _ = t * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ * t / δ) := by
          congr 2
          field_simp

/-- A positive `ε` at least `δ / (2 * (Λ * t))` makes `t * sqrt (Λ1 * Λmax * D / ε)` at most
`sqrt 2 * lemma8QueryExpr`, under the stated positivity hypotheses. See [Berry and Childs,
Lemma 8][BerryChilds2012]. -/
theorem lemma8_query_bound {Λ Λ1 Λmax ε t δ : ℝ} {D : ℕ}
    (hΛ : 0 < Λ) (hΛ1 : 0 < Λ1) (hD : 0 < D) (ht : 0 < t) (hδ : 0 < δ)
    (hmax0 : 0 ≤ Λmax) (hε0 : 0 < ε)
    (hεge : δ / (2 * (Λ * t)) ≤ ε) :
    t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε) ≤
      Real.sqrt 2 * lemma8QueryExpr Λ Λ1 Λmax D t δ := by
  rw [lemma8QueryExpr_eq hΛ hΛ1 hD ht hδ hmax0]
  have hmul : δ ≤ ε * (2 * (Λ * t)) := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (Λ * t))] at hεge
    linarith
  have hbase : 0 ≤ Λ1 * Λmax * (D : ℝ) := by positivity
  have hkey : Λ1 * Λmax * (D : ℝ) * δ ≤ (2 * (Λmax * (D : ℝ) * Λ1 * Λ * t)) * ε := by
    have := mul_le_mul_of_nonneg_left hmul hbase
    nlinarith [this]
  have hineq : Λ1 * Λmax * (D : ℝ) / ε ≤
      2 * (Λmax * (D : ℝ) * Λ1 * Λ * t / δ) := by
    rw [div_le_iff₀ hε0]
    rw [show 2 * (Λmax * (D : ℝ) * Λ1 * Λ * t / δ) * ε =
      2 * (Λmax * (D : ℝ) * Λ1 * Λ * t) * ε / δ by ring]
    rw [le_div_iff₀ hδ]
    nlinarith [hkey]
  have hsqrt := Real.sqrt_le_sqrt hineq
  have hsplit : Real.sqrt (2 * (Λmax * (D : ℝ) * Λ1 * Λ * t / δ)) =
      Real.sqrt 2 * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ * t / δ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε)
      ≤ t * Real.sqrt (2 * (Λmax * (D : ℝ) * Λ1 * Λ * t / δ)) := by
        exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt ht)
    _ = t * (Real.sqrt 2 * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ * t / δ)) := by rw [hsplit]
    _ = Real.sqrt 2 * (t * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ * t / δ)) := by ring

/-- Under the stated black box, norm, and parameter hypotheses, choose a positive `ε ≤ 1`
between `δ / (2 * (Λ * t))` and `δ / (Λ * t)` and establish the accompanying scalar cost
identity and bound. This packages the parameter arithmetic for Lemma 8 of [BerryChilds2012]. -/
theorem lemma8_improved_simulation
    (BB : BlackBox ι D L) {Λ Λ1 Λmax t δ : ℝ}
    (hsp : IsColumnSparse BB.H D) (hD : 0 < D)
    (hΛ : spectralNorm BB.H ≤ Λ) (hΛ1 : colSumNorm BB.H ≤ Λ1)
    (hΛmax : maxEntryNorm BB.H ≤ Λmax)
    (hΛ0 : 0 < Λ) (hΛ1pos : 0 < Λ1) (hmax0 : 0 < Λmax)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t)
    (hcond1 : Real.sqrt δ ≤ Λ * t)
    (hcond2 : Λ / (Λmax * Λ1 * (D : ℝ)) ≤ Λ * t)
    (hcond3 : Λ ≤ Λ1)
    (hden : 0 < Λmax * Λ1 * (D : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ / (Λ * t) ∧ ε ≤ 1 ∧
      δ / (2 * (Λ * t)) ≤ ε ∧
      (Λ1 * t / ε) * Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) =
        t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε) ∧
      t * Real.sqrt (Λ1 * Λmax * (D : ℝ) / ε) ≤
        Real.sqrt 2 * lemma8QueryExpr Λ Λ1 Λmax D t δ := by
  have ht0 : 0 < t := by
    have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
    have hΛt : 0 < Λ * t := lt_of_lt_of_le hs hcond1
    exact pos_of_mul_pos_right hΛt hΛ0.le
  have hratio : 1 ≤ Λ1 * Λ * t ^ 2 / δ :=
    lemma8_ratio_ge_one hδ0 ht0 hΛ0 hcond1 hcond3
  have hε0 : 0 < lemma8Eps Λ1 Λ t δ := lemma8_eps_pos hδ0 ht0 hΛ0 hΛ1pos
  exact ⟨lemma8Eps Λ1 Λ t δ, hε0,
    lemma8_eps_le_delta hδ0 ht0 hΛ0 hΛ1pos,
    lemma8_eps_le_one hδ0 hδ1 ht0 hΛ0 hΛ1pos hcond1,
    lemma8_eps_ge_half hδ0 ht0 hΛ0 hΛ1pos hratio,
    lemma8_query_identity (D := D) hε0 hΛ1pos hmax0.le,
    lemma8_query_bound hΛ0 hΛ1pos hD ht0 hδ0 hmax0.le hε0
      (lemma8_eps_ge_half hδ0 ht0 hΛ0 hΛ1pos hratio)⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse
