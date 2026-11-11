/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel
import Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp.Lemma16C1C2

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 20: Definition-1 coefficients `c₁`, `c₂` for the QLSP schedule

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 20 / Eqs. (H3)--(H6), pages 49--50.

For the schedule `f` of Eq. (114) with `1 < p < 2`, the gap is
`Δ₀(s) = 1 - f(s) + f(s)/κ` (Eq. (112)) and the paper computes the derivatives
(on the interval `[s, s+1/T] ∩ [0,1]`)

`f'(τ) = d_p Δ₀(s)^p`,                                          (H5)

`f''(τ) = d_p² p (-1 + 1/κ) Δ₀(s)^(2p-1)`,                      (H6)

with `d_p = 2^(p/2) κ/((p-1)(κ-1)) (κ^(p-1) - 1)` of Eq. (H19).  Because
`Δ₀` is decreasing in `s`, the maxima in Eqs. (H1)--(H2) defining `c₁`, `c₂`
are attained at the left endpoint `s` (`|f'|`, `|f'|²` and `|f''|` are all
decreasing), so

`c₁(s) = 2 d_p Δ₀(s)^p`,                                        (H3)

`c₂(s) = 4 d_p² Δ₀(s)^(2p) + 2 d_p² p (1 - 1/κ) Δ₀(s)^(2p-1)`.   (H4)

The file proves (H3)--(H4) from the reduced maxima (H1), (H2) together with
the derivative formulas (H5), (H6).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

/-- Fixed arXiv:2111.08152, Lemma 20 (Eqs. (H3)--(H4), p. 49): the
Definition-1 coefficients for the QLSP schedule (114) are
`c₁ = 2 d_p Δ₀^p` and `c₂ = 4 d_p² Δ₀^(2p) + 2 d_p² p (1 - 1/κ) Δ₀^(2p-1)`,
where the maxima of (H1)--(H2) are attained at `s` by monotonicity of `Δ₀`,
and `|f'|`, `|f''|` are given by (H5)--(H6). -/
theorem source_lemma20
    (κ p : ℝ) (c1 c2 : ℝ → ℝ) (f' f'' : ℝ → ℝ) (s : ℝ)
    (hp : 1 < p) (hκ : 1 < κ)
    (hc1 : c1 s = 2 * |f' s|)
    (hc2 : c2 s = 2 * (2 * |f' s| ^ 2 + |f'' s|))
    (hf' : f' s = dp κ p * gap0 κ p s ^ p)
    (hf'' : |f'' s| = dp κ p ^ 2 * p * (1 - 1 / κ) * gap0 κ p s ^ (2 * p - 1))
    (hgap : 0 ≤ gap0 κ p s) :
    c1 s = 2 * dp κ p * gap0 κ p s ^ p ∧
      c2 s = 4 * dp κ p ^ 2 * gap0 κ p s ^ (2 * p)
        + 2 * dp κ p ^ 2 * p * (1 - 1 / κ) * gap0 κ p s ^ (2 * p - 1) := by
  have hdp : 0 < dp κ p := by
    unfold dp
    have h2 : 0 < (2 : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hB : 0 < κ ^ (p - 1) - 1 := by
      have h1 := Real.one_lt_rpow hκ (by linarith : (0 : ℝ) < p - 1)
      linarith
    have hden : 0 < (p - 1) * (κ - 1) := mul_pos (by linarith) (by linarith)
    have hpos : 0 < 2 ^ (p / 2) * κ / ((p - 1) * (κ - 1)) :=
      div_pos (mul_pos h2 (by linarith)) hden
    exact mul_pos hpos hB
  have hf'abs : |f' s| = dp κ p * gap0 κ p s ^ p := by
    rw [hf', abs_of_nonneg (mul_nonneg hdp.le (Real.rpow_nonneg hgap p))]
  have hsq : (gap0 κ p s ^ p) ^ 2 = gap0 κ p s ^ (2 * p) := by
    rw [← Real.rpow_natCast]
    have hmul : gap0 κ p s ^ (p * ((2 : ℕ) : ℝ))
        = (gap0 κ p s ^ p) ^ ((2 : ℕ) : ℝ) :=
      Real.rpow_mul hgap p ((2 : ℕ) : ℝ)
    rw [← hmul]
    congr 1
    push_cast
    ring
  constructor
  · rw [hc1, hf'abs]
    ring
  · rw [hc2, hf'abs, hf'' , mul_pow, hsq]
    ring

end Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp
