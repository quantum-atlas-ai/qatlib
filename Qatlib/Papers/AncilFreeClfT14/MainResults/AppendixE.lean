/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.AncilFreeClfT14.MainResults.CoreModel

/-!
# Appendix E — elementary inequalities (Lemma E.1)

Source: N. J. Ross and P. Selinger, *Optimal ancilla-free Clifford+T
approximation of z-rotations*, arXiv:1403.2975v3, Lemma E.1 (p. 38).

Lemma E.1 states three elementary calculus facts:
(a) `√x ≥ ln x` for all `x > 0`;
(b) `3√x ≥ (ln x)²` for all `x ≥ 1`;
(c) `(1 - a/x)^x ≤ e^{-a}` for all `x ≥ a > 0`.

The paper proves them "by elementary calculus".  We give complete proofs.
The key uniform estimate is `log t ≤ t/e`, proved from `log y ≤ y - 1`
applied to `y = t/e`; both (a) and (b) follow from it by substituting
`t = √x`, resp. `t = √(√x)` (the paper's second substitution inspects the
maxima of `(ln x)²/(3√x)` at `x = e⁴`, which is the same computation).
-/

/-!
# AppendixE

Paper-layer definitions and source results for AncilFreeClfT14.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Real

namespace Qatlib.Papers.AncilFreeClfT14.MainResults

/-- The sharp logarithmic estimate `log t ≤ t/e` for `t > 0`, obtained by
applying `log y ≤ y - 1` at `y = t/e`.  This is the step the paper hides
behind "elementary calculus". -/
theorem log_le_div_exp_one {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ t / Real.exp 1 := by
  rw [Real.log_le_iff_le_exp ht]
  -- It suffices to prove `t ≤ exp (t/e)`, which follows from `u ≤ exp (u-1)`.
  have h := Real.add_one_le_exp (t / Real.exp 1 - 1)
  have h' : t / Real.exp 1 ≤ Real.exp (t / Real.exp 1 - 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left h' (le_of_lt (Real.exp_pos 1))
  have heq : Real.exp 1 * Real.exp (t / Real.exp 1 - 1) = Real.exp (t / Real.exp 1) := by
    rw [← Real.exp_add]
    ring_nf
  have hdiv : Real.exp 1 * (t / Real.exp 1) = t := by
    field_simp
  calc t = Real.exp 1 * (t / Real.exp 1) := hdiv.symm
    _ ≤ Real.exp 1 * Real.exp (t / Real.exp 1 - 1) := hmul
    _ = Real.exp (t / Real.exp 1) := heq

/-- **Lemma E.1(a).** `√x ≥ ln x` for all `x > 0` (arXiv:1403.2975v3, Lemma
E.1(a), p. 38).  Proof: `log x = 2 log √x ≤ 2 (√x)/e ≤ √x` since `e ≥ 2`. -/
theorem lemma_E1_a {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x / Real.exp 1 :=
    log_le_div_exp_one hs
  have he2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have hsnn : 0 ≤ Real.sqrt x := le_of_lt hs
  have h2 : Real.sqrt x / Real.exp 1 ≤ Real.sqrt x / 2 :=
    div_le_div_of_nonneg_left hsnn (by norm_num) he2
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hx)]
    ring
  rw [hlog]
  linarith

/-- **Lemma E.1(b).** `3√x ≥ (ln x)²` for all `x ≥ 1` (arXiv:1403.2975v3,
Lemma E.1(b), p. 38).  Proof: writing `t = √(√x)`, `log x = 4 log t ≤ 4t/e`,
and `16/e² ≤ 3` because `e > 2.71828`. -/
theorem lemma_E1_b {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 3 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  set s : ℝ := Real.sqrt x with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hs1 : 1 ≤ s := by
    rw [hs_def]
    exact Real.one_le_sqrt.2 hx
  set t : ℝ := Real.sqrt s with ht_def
  have ht0 : 0 < t := Real.sqrt_pos.2 hs0
  have ht1 : 1 ≤ t := by
    rw [ht_def]
    exact Real.one_le_sqrt.2 hs1
  -- `log x = 4 log t`
  have hlx : Real.log x = 4 * Real.log t := by
    have e1 : Real.log x = 2 * Real.log s := by
      rw [hs_def, Real.log_sqrt (le_of_lt hx0)]
      ring
    have e2 : Real.log s = 2 * Real.log t := by
      rw [ht_def, Real.log_sqrt (le_of_lt hs0)]
      ring
    rw [e1, e2]
    ring
  -- `t² = √x`
  have ht2 : t ^ 2 = Real.sqrt x := by
    rw [ht_def, Real.sq_sqrt (le_of_lt hs0)]
  have hlogt : Real.log t ≤ t / Real.exp 1 := log_le_div_exp_one ht0
  have hlogt_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hquot_nn : 0 ≤ t / Real.exp 1 := by positivity
  have hsq : (Real.log t) ^ 2 ≤ (t / Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ hlogt_nn hlogt 2
  have hquot_sq : (t / Real.exp 1) ^ 2 = t ^ 2 / (Real.exp 1) ^ 2 := by
    ring
  have hconst : 16 ≤ 3 * (Real.exp 1) ^ 2 := by
    nlinarith [Real.exp_one_gt_d9]
  have hexp_pos : 0 < (Real.exp 1) ^ 2 := by positivity
  -- combine: `(log x)² = 16 (log t)² ≤ 16 t²/e² = (16/e²) √x ≤ 3 √x`
  have hfin : 16 * (Real.log t) ^ 2 ≤ 16 * (t / Real.exp 1) ^ 2 := by
    nlinarith
  have hsqx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc (Real.log x) ^ 2 = 16 * (Real.log t) ^ 2 := by rw [hlx]; ring
    _ ≤ 16 * (t / Real.exp 1) ^ 2 := hfin
    _ = 16 / (Real.exp 1) ^ 2 * t ^ 2 := by rw [hquot_sq]; ring
    _ = 16 / (Real.exp 1) ^ 2 * Real.sqrt x := by rw [ht2]
    _ ≤ 3 * Real.sqrt x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hexp_pos]
        nlinarith

/-- **Lemma E.1(c).** `(1 - a/x)^x ≤ e^{-a}` for all `x ≥ a > 0`
(arXiv:1403.2975v3, Lemma E.1(c), p. 38).  We state it with the real
`rpow`, exactly as the paper does; the proof applies `z + 1 ≤ e^z` at
`z = -a/x` and then raises to the power `x`. -/
theorem lemma_E1_c {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    (1 - a / x) ^ x ≤ Real.exp (-a) := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  -- `z + 1 ≤ exp z` at `z = -a/x`
  have hz := Real.add_one_le_exp (-(a / x))
  have hbase : 1 - a / x ≤ Real.exp (-(a / x)) := by
    have : -(a / x) + 1 = 1 - a / x := by ring
    linarith
  have hbase_nn : 0 ≤ 1 - a / x := by
    have : a / x ≤ 1 := by
      rw [div_le_one hx]
      exact hax
    linarith
  have hxnn : 0 ≤ x := le_of_lt hx
  have hstep : (1 - a / x) ^ x ≤ (Real.exp (-(a / x))) ^ x :=
    Real.rpow_le_rpow hbase_nn hbase hxnn
  have hexp : (Real.exp (-(a / x))) ^ x = Real.exp (-a) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rwa [hexp] at hstep

/-- **Lemma E.1.** The three inequalities of Lemma E.1 together, as stated in
arXiv:1403.2975v3, Appendix E, p. 38. -/
theorem lemma_E1 :
    (∀ x : ℝ, 0 < x → Real.log x ≤ Real.sqrt x) ∧
    (∀ x : ℝ, 1 ≤ x → (Real.log x) ^ 2 ≤ 3 * Real.sqrt x) ∧
    (∀ a x : ℝ, 0 < a → a ≤ x → (1 - a / x) ^ x ≤ Real.exp (-a)) :=
  ⟨fun _ hx => lemma_E1_a hx, fun _ hx => lemma_E1_b hx,
   fun _ _ ha hax => lemma_E1_c ha hax⟩

end Qatlib.Papers.AncilFreeClfT14.MainResults
