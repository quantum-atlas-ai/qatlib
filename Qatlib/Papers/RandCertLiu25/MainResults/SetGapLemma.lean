/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 13: a threshold with an additive set-size gap

Formalises the indicator case of Lemma 13 of Liu--Shaydulin--Niroula et al.,
*Certified randomness using a trapped-ion quantum processor*, fixed
arXiv:2503.20498v1, Lemma 13 and Eq. I.29, p. 6.

Statement (paper).  Let `ε ∈ [0,1]` and `δ, a0, a1 ∈ (0,1]` with
`a1 = a0 + δ ≤ (1+ε/8)a0`.  Let `X0, X1` be random variables in `[0,1]` such
that `Xb > 0 ⇒ Xb ≥ ab`, and `E[X1] ≥ (1+ε) E[X0]`.  Then there is a rational
`t` with `1 ≥ t ≥ a0` such that

  `Pr[X1 > t + δ/2] ≥ (1 + ε/4) Pr[X0 > t] + (ε/8) E[X1]`.     (I.29)

Formalisation.  The paper proves the general case with a continuous
layer-cake identity and a pigeonhole over a `2/δ` grid.  The only place the
lemma is consumed, Corollary 14, instantiates `X_b` as the indicator
`Y_τ(C, s) ∈ {0,1}`.  We formalise exactly that instance: for `{0,1}`-valued
`X0, X1` and rational `a0`, the threshold `t = a0` already works.  Indeed
`Pr[Xb > ab] = E[Xb]` and `Pr[X1 > a0 + δ/2] = E[X1]` because
`a0 + δ/2 < a1 ≤ 1`; the inequality then reduces to
`(1+ε/4) E[X0] ≤ (1-ε/8) E[X1]`, which follows from
`E[X1] ≥ (1+ε) E[X0]` and `ε ≤ 1`.

This is a faithful restricted instance of (I.29): the general continuous
layer-cake split of Eqs. I.30--I.35 is not reproduced, and the `2/δ`-grid
pigeonhole is unnecessary for the indicator application.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.SetGapLemma

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- `Pr[X > c]` for a real-valued observable on a finite probability space. -/
def probGT {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinDist Ω)
    (X : Ω → ℝ) (c : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => c < X ω), P.prob ω

/-- For a `{0,1}`-valued observable and `0 < c < 1`, the tail mass
`Pr[X > c]` equals the expectation `E[X]`. -/
theorem probGT_of_zero_one {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinDist Ω) (X : Ω → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) :
    probGT P X c = P.expect X := by
  unfold probGT FinDist.expect
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  rcases hX ω with h | h
  · rw [h]
    simp [not_lt.mpr hc0.le]
  · rw [h]
    simp [hc1]

/-- **Lemma 13, indicator case** (Eq. I.29).  For `{0,1}`-valued `X0, X1`
with rational `a0`, the threshold `t = a0` satisfies the additive set-size
gap, provided `a0 + δ/2 < 1` and the mean gap `E[X1] ≥ (1+ε)E[X0]`.  The
general layer-cake case split of the paper is not needed for this instance. -/
theorem lemma13_set_gap_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinDist Ω) (X0 X1 : Ω → ℝ) (eps delta a0 a1 : ℚ)
    (heps0 : 0 ≤ (eps : ℝ)) (heps1 : (eps : ℝ) ≤ 1)
    (hdelta : 0 < (delta : ℝ)) (ha0 : 0 < (a0 : ℝ))
    (hle : (a0 : ℝ) ≤ 1)
    (hlt : (a0 : ℝ) + (delta : ℝ) / 2 < 1)
    (hsum : (a1 : ℝ) = (a0 : ℝ) + (delta : ℝ))
    (hratio : (a1 : ℝ) ≤ (1 + (eps : ℝ) / 8) * (a0 : ℝ))
    (hX0 : ∀ ω, X0 ω = 0 ∨ X0 ω = 1)
    (hX1 : ∀ ω, X1 ω = 0 ∨ X1 ω = 1)
    (hE : (1 + (eps : ℝ)) * P.expect X0 ≤ P.expect X1) :
    ∃ t : ℚ, (a0 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 ∧
      (1 + (eps : ℝ) / 4) * probGT P X0 (t : ℝ) + ((eps : ℝ) / 8) * P.expect X1 ≤
        probGT P X1 ((t : ℝ) + (delta : ℝ) / 2) := by
  have ha0_lt_one : (a0 : ℝ) < 1 := by linarith
  have hcpos : 0 < (a0 : ℝ) + (delta : ℝ) / 2 := by linarith
  have hE0 : 0 ≤ P.expect X0 := by
    unfold FinDist.expect
    apply Finset.sum_nonneg
    intro ω _
    rcases hX0 ω with h | h
    · rw [h]
      simp
    · rw [h]
      simpa using P.nonneg ω
  have hcoef : (1 + (eps : ℝ) / 4) ≤
      (1 - (eps : ℝ) / 8) * (1 + (eps : ℝ)) := by
    nlinarith [heps0, heps1]
  have hmul1 : (1 + (eps : ℝ) / 4) * P.expect X0 ≤
      ((1 - (eps : ℝ) / 8) * (1 + (eps : ℝ))) * P.expect X0 :=
    mul_le_mul_of_nonneg_right hcoef hE0
  have hmul2 : (1 - (eps : ℝ) / 8) * ((1 + (eps : ℝ)) * P.expect X0) ≤
      (1 - (eps : ℝ) / 8) * P.expect X1 :=
    mul_le_mul_of_nonneg_left hE (by linarith)
  have hmain : (1 + (eps : ℝ) / 4) * P.expect X0 ≤
      (1 - (eps : ℝ) / 8) * P.expect X1 := by
    calc (1 + (eps : ℝ) / 4) * P.expect X0
        ≤ ((1 - (eps : ℝ) / 8) * (1 + (eps : ℝ))) * P.expect X0 := hmul1
      _ = (1 - (eps : ℝ) / 8) * ((1 + (eps : ℝ)) * P.expect X0) := by ring
      _ ≤ (1 - (eps : ℝ) / 8) * P.expect X1 := hmul2
  refine ⟨a0, le_rfl, hle, ?_⟩
  rw [probGT_of_zero_one P X0 (a0 : ℝ) ha0 ha0_lt_one hX0,
    probGT_of_zero_one P X1 ((a0 : ℝ) + (delta : ℝ) / 2) hcpos hlt hX1]
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.SetGapLemma
