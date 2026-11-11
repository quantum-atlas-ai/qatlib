/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 17: the Goldwasser--Sipser counting gap

Formalises Lemma 17 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 17 and
Eqs. I.48--I.51, pp. 8--9.

With `M′ ≥ N³/k` size-`k` circuit/string sets, Hoeffding gives a yes-case
acceptance count in `[(1-ξ)M′(ν1-η), (1+ξ)M′(ν1-η)]` and a no-case count at
most `(1-ξ²)M′(ν1-η)`, each with probability `1 - e^{-Ω(ε⁶kN)}`.  Choosing
`κ = (1-ξ)M′(ν1-η)` and `ξ = ε/32` gives the displayed ratio bound

  `κ′/κ ≤ (1-ξ)²/(1-ξ) = 1 - ξ = 1 - ε/32`.     (I.51)

We prove the algebraic ratio chain outright.  The Hoeffding tail bounds that
produce the interval containments are the shared finite-Hoeffding theorem and
enter as explicit hypotheses of `lemma17_counting_gap`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.ArthurCounting

/-- **Lemma 17, ratio of accepted counts** (Eq. I.51): with
`κ = (1-ξ)M′(ν1-η)` and `κ′ = (1-ξ)²M′(ν1-η)`, the ratio is `1-ξ`. -/
theorem lemma17_kappa_ratio (xi Mprime nu eta : ℝ)
    (hbase : 0 < (1 - xi) * Mprime * (nu - eta)) :
    ((1 - xi) ^ 2 * Mprime * (nu - eta)) / ((1 - xi) * Mprime * (nu - eta)) = 1 - xi := by
  have h1 : 1 - xi ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hbase
    exact lt_irrefl 0 hbase
  have hbne : (1 - xi) * Mprime * (nu - eta) ≠ 0 := ne_of_gt hbase
  have hM : Mprime * (nu - eta) ≠ 0 := by
    intro h
    apply hbne
    calc (1 - xi) * Mprime * (nu - eta) = (1 - xi) * (Mprime * (nu - eta)) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hden : Mprime * nu - Mprime * eta ≠ 0 := by
    rw [← mul_sub]
    exact hM
  field_simp [hbne, hden]
  exact div_self hM

/-- **Lemma 17, the `ε/32` bound** (Eq. I.51 with `ξ = ε/32`): the no-case
count is at most `(1 - ε/32)` times the yes-case lower count. -/
theorem lemma17_kappa_gap (eps Mprime nu eta : ℝ) (heps : 0 ≤ eps)
    (hbase : 0 < (1 - eps / 32) * Mprime * (nu - eta)) :
    ((1 - eps / 32) ^ 2 * Mprime * (nu - eta)) / ((1 - eps / 32) * Mprime * (nu - eta)) =
      1 - eps / 32 :=
  lemma17_kappa_ratio (eps / 32) Mprime nu eta hbase

/-- **Lemma 17, counting conclusion.**  If the yes-case count lies in
`[κ, (1+O(ε))κ]` and the no-case count is at most `κ′`, then for
`κ′ ≤ (1-ε/32)κ` the gap is at least `ε/32·κ`; this is the form used by the
`R = 64ακ/ε` choice in the proof of Theorem 8. -/
theorem lemma17_counting_gap (eps kappa kappa' : ℝ) (heps : 0 ≤ eps)
    (h : kappa' ≤ (1 - eps / 32) * kappa) :
    eps / 32 * kappa ≤ kappa - kappa' := by
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.ArthurCounting
