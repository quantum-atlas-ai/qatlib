/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Source Corollary 1 — the combined running-time / success-probability ratio

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Corollary 1 is printed on p.11 (§4.2).

The source combines Lemma 7 (the `l₂`-average running time)

  `T_av = O(√(∑_i |α_i|² 2^{2 j_i}) · k_uniq)`   (eq. (11))

with Lemma 8 (the success probability)

  `p_succ = Ω(∑_i |α_i|² ε² 2^{2 j_i}/κ²)`   (eq. (12))

and divides them.  The `∑_i |α_i|² 2^{2 j_i}` sum cancels, the `ε/κ` factor
in the denominator turns into `κ/ε` in the ratio, and the result is

  `T_av/√p_succ = O((κ/ε) k_uniq)`   (Corollary 1).

The Lean statement below is that arithmetic combination with the two `O`/`Ω`
absolute constants (`C_T` from eq. (11) and the `1/4` from eq. (12) — the
constant that Lemma 8's `Ω` hides) made explicit.  The `Ω` in Lemma 8 is
represented by its witnessing constant `1/4` as in
`SourceLemma8.source_lemma8`; the `O` in Lemma 7 is represented by a constant
`C_T ≥ 0` multiplying `√(∑_i |α_i|² 2^{2 j_i})` and the `k_uniq` factor.  No
extra hypothesis is introduced: the only assumption beyond nonnegativity of
the constants is that the surviving weighted sum is positive, which is
exactly what makes the quotient well defined.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

/-- Fixed arXiv:1010.4458v2, Corollary 1 (printed p.11).

Let `S = ∑_i |α_i|² 2^{2 j_i}` be the weighted leading-stage sum.  If the
average running time obeys the Lemma 7 order
`T_av ≤ C_T · k_uniq · √S` and the success probability obeys the Lemma 8
order `p_succ ≥ (1/4)·∑_i |α_i|² ε² 2^{2 j_i}/κ²`, then

  `T_av/√p_succ ≤ 2 · C_T · k_uniq · (κ/ε)`,

which is the source's `O((κ/ε) k_uniq)` with the absolute constant
`2·C_T` exposed (the `1/4` of Lemma 8 contributes the factor `2`). -/
theorem source_corollary1 {ι : Type} [Fintype ι]
    (α : ι → ℝ) (j : ι → ℕ) (Tav psucc CT kuniq ε κ : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hCT : 0 ≤ CT) (hk : 0 ≤ kuniq)
    (hS : 0 < ∑ i, α i ^ 2 * (2 : ℝ) ^ (2 * j i))
    (hT : Tav ≤ CT * kuniq * Real.sqrt (∑ i, α i ^ 2 * (2 : ℝ) ^ (2 * j i)))
    (hp : (1 / 4) * (∑ i, α i ^ 2 * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2) ≤ psucc) :
    Tav / Real.sqrt psucc ≤ 2 * CT * kuniq * (κ / ε) := by
  classical
  set S : ℝ := ∑ i, α i ^ 2 * (2 : ℝ) ^ (2 * j i) with hS_def
  -- The Lemma 8 sum factors as `(ε²/κ²)·S`.
  have hfac : (∑ i, α i ^ 2 * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2)
      = (ε ^ 2 / κ ^ 2) * S := by
    rw [hS_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hp' : (1 / 4) * ((ε ^ 2 / κ ^ 2) * S) ≤ psucc := by
    rw [hfac] at hp
    exact hp
  -- The gain coefficient `(1/2)·(ε/κ)` is positive.
  have hcoef : 0 < (1 / 2) * (ε / κ) :=
    mul_pos (by norm_num) (div_pos hε hκ)
  have hsqrtS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hden : 0 < (1 / 2) * (ε / κ) * Real.sqrt S := mul_pos hcoef hsqrtS
  -- `√(p_succ) ≥ (1/2)(ε/κ)√S`, from the Lemma 8 bound.
  have hsq : (1 / 2) * (ε / κ) * Real.sqrt S ≤ Real.sqrt psucc := by
    have harg : (1 / 4) * ((ε ^ 2 / κ ^ 2) * S) = ((1 / 2) * (ε / κ)) ^ 2 * S := by
      ring
    have := Real.sqrt_le_sqrt hp'
    rwa [harg, Real.sqrt_mul (sq_nonneg ((1 / 2) * (ε / κ))),
      Real.sqrt_sq (le_of_lt hcoef)] at this
  -- Ratio bound: numerator `≤ C_T·k_uniq·√S`, denominator `≥ (1/2)(ε/κ)√S`.
  have hC0 : 0 ≤ CT * kuniq := mul_nonneg hCT hk
  have hstep1 : Tav / Real.sqrt psucc
      ≤ (CT * kuniq * Real.sqrt S) / Real.sqrt psucc :=
    div_le_div_of_nonneg_right hT (Real.sqrt_nonneg _)
  have hstep2 : (CT * kuniq * Real.sqrt S) / Real.sqrt psucc
      ≤ (CT * kuniq * Real.sqrt S) / ((1 / 2) * (ε / κ) * Real.sqrt S) :=
    div_le_div_of_nonneg_left (mul_nonneg hC0 (Real.sqrt_nonneg _)) hden hsq
  have hstep3 : (CT * kuniq * Real.sqrt S) / ((1 / 2) * (ε / κ) * Real.sqrt S)
      = 2 * CT * kuniq * (κ / ε) := by
    have hcoef_ne : (1 / 2) * (ε / κ) ≠ 0 := ne_of_gt hcoef
    have hsqrt_ne : Real.sqrt S ≠ 0 := ne_of_gt hsqrtS
    field_simp
  exact hstep1.trans (hstep2.trans hstep3.le)

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
