/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.DeltaRegion
import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceLemma13

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 8 — errors from a finite `Δ` occur only at the last step

Source: arXiv:2105.02859v3, Theorem 8 (Sec. V A 2, metadata lines 900--906;
Eq. (70)), Appendix B "Theorem 8" (Eqs. (B13)--(B18)) and Fig. 18.

If `Δ < 2 (cos(3π/16) − 1/√2)` then a `Δ`-region hit — hence an error of the
QSVT sign-function evaluation — can only occur at the last iteration
`j = n-1`; an error made there contributes at most `2^{-n}` to the final phase
error, assuming no later errors.

Formalized content (this file):

* `source_theorem8_delta_choice`: condition (70) implies condition (B16) of
  Lemma 13, using the strict inequality
  `cos(3π/16) + cos(5π/16) < √2` (`cos3_plus_cos5_lt_sqrt_two`);
* `source_theorem8_region_avoidance`: at a single iteration whose deviation has
  the Lemma-12 form `b + e`, `b ∈ {0, 1/2}`, `|e| ≤ 1/8` (paper Eqs. (B17),
  (B18): `r̃_{n-1} = 0` gives a deviation `≤ 1/8` around `0.φ_{n-1}`, and
  `r̃_{n-1} = 1` gives `0.φ[n-1:] > 0.11 = 1/4 + 1/8`), the region is not hit;
* `source_theorem8_region_only_last`: consequently, if every early iteration
  `j ≤ n-2` admits such a two-bit localization of its deviation, the region is
  hit only at `j = n-1`;
* `source_theorem8_error_bound`: a last-step error of size at most `1/2` at
  the `2^{-(n-1)}` scale is below `2^{-n}`.

Boundary (part of the paper's proof not formalized): the derivation of the
two-bit localization from the rounding bound of Lemma 12 for **all** early
iterations `j ≤ n-2` (the recursive step of the paper's argument) is supplied
here as the explicit hypothesis `hloc`.  The arithmetic of the paper's own
stages is proved; the induction tying `hloc` to `source_lemma12_half_pow` is
the remaining gap and is recorded in the PR notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

open scoped Real

/-- GrandUnif21 Theorem 8, Eq. (70) ⇒ Lemma 13 condition (B16): if
`Δ ≥ 0` and `Δ < 2 (cos(3π/16) − 1/√2)`, then
`1/4 − (1/π) arccos(1/√2 + Δ/2) < 1/16`. -/
theorem source_theorem8_delta_choice {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * π / 16) - 1 / Real.sqrt 2)) :
    1 / 4 - (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) < 1 / 16 := by
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hxlt : 1 / Real.sqrt 2 + Δ / 2 < Real.cos (3 * π / 16) := by linarith
  have hxge : -1 ≤ 1 / Real.sqrt 2 + Δ / 2 := by
    have hcpos : 0 < 1 / Real.sqrt 2 := by positivity
    linarith
  have hcos1 : Real.cos (3 * π / 16) ≤ 1 := Real.cos_le_one _
  have hgt : 3 * π / 16 < Real.arccos (1 / Real.sqrt 2 + Δ / 2) := by
    have h := Real.arccos_lt_arccos (x := 1 / Real.sqrt 2 + Δ / 2)
      (y := Real.cos (3 * π / 16)) hxge hxlt hcos1
    have h3 : Real.arccos (Real.cos (3 * π / 16)) = 3 * π / 16 :=
      Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
    rwa [h3] at h
  have h1 : (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) > 1 / 4 - 1 / 16 := by
    have hm := mul_lt_mul_of_pos_left hgt (show (0 : ℝ) < 1 / π by positivity)
    have h3 : (1 / π) * (3 * π / 16) = 3 / 16 := by field_simp
    linarith
  linarith

/-- GrandUnif21 Theorem 8, Appendix B (B17)--(B18): if the deviation
`b + e` at an iteration has a leading digit `b ∈ {0, 1/2}` and a remainder
`|e| ≤ 1/8`, then the `Δ`-region (under Eq. (70)) is not hit there. -/
theorem source_theorem8_region_avoidance {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * π / 16) - 1 / Real.sqrt 2))
    {b e : ℝ} (hb : b = 0 ∨ b = 1 / 2) (he : |e| ≤ 1 / 8)
    (hy : |b + e| ≤ 1) :
    ¬ (|Real.cos (π * (b + e))| ∈
      Set.Icc (1 / Real.sqrt 2 - Δ / 2) (1 / Real.sqrt 2 + Δ / 2)) := by
  intro hreg
  have hB16 := source_theorem8_delta_choice hΔ0 hΔ
  have h := source_lemma13 hΔ0 hB16 hy hreg
  have he' : -(1 / 8) ≤ e ∧ e ≤ 1 / 8 := abs_le.mp he
  rcases hb with hb0 | hb1
  · subst hb0
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : (1 / 4 - 1 / 16 : ℝ) < |e| := by simpa using h1
      linarith
    · have h1' : (3 / 4 - 1 / 16 : ℝ) < |e| := by simpa using h1
      linarith
  · subst hb1
    have hpos : 0 ≤ 1 / 2 + e := by linarith
    have habs : |1 / 2 + e| = 1 / 2 + e := abs_of_nonneg hpos
    rw [habs] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith

/-- GrandUnif21 Theorem 8, "only possible at `j = n-1`": if at every early
iteration `j ≤ n-2` the deviation `dev j = 0.φ[j+1:] − θ_j` has the two-bit
form `b + e` with `b ∈ {0, 1/2}` and `|e| ≤ 1/8` (the Lemma-12 localization of
Eqs. (B17)--(B18)), then no early iteration hits the `Δ`-region. -/
theorem source_theorem8_region_only_last {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * π / 16) - 1 / Real.sqrt 2))
    {n : ℕ} {dev : ℕ → ℝ}
    (hdev : ∀ j, j ≤ n - 2 → |dev j| ≤ 1)
    (hloc : ∀ j, j ≤ n - 2 → ∃ b e : ℝ, (b = 0 ∨ b = 1 / 2) ∧ |e| ≤ 1 / 8 ∧ dev j = b + e) :
    ∀ j, j ≤ n - 2 →
      ¬ (|Real.cos (π * (dev j))| ∈
        Set.Icc (1 / Real.sqrt 2 - Δ / 2) (1 / Real.sqrt 2 + Δ / 2)) := by
  intro j hj
  obtain ⟨b, e, hb, he, hde⟩ := hloc j hj
  rw [hde]
  exact source_theorem8_region_avoidance hΔ0 hΔ hb he (by simpa [hde] using hdev j hj)

/-- GrandUnif21 Theorem 8, error bound at the last iteration: an error of size
`e < 1/2` at the `2^{-(n-1)}` scale of the last tail, with `n ≥ 1`, makes the
final phase error smaller than `2^{-n}`. -/
theorem source_theorem8_error_bound {e : ℝ} (he0 : 0 ≤ e) (he : e < 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ (n - 1) * e < 1 / (2 : ℝ) ^ n := by
  have hstep : (1 / 2 : ℝ) ^ (n - 1) * (1 / 2) = (1 / 2 : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  calc (1 / 2 : ℝ) ^ (n - 1) * e < (1 / 2 : ℝ) ^ (n - 1) * (1 / 2) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ n := hstep
    _ = 1 / (2 : ℝ) ^ n := by
        rw [div_pow, one_pow]

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
