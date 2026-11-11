/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.PayoffMean

set_option backward.isDefEq.respectTransparency false

/-!
# The source VaR threshold readout and its exact bisection

Woerner--Egger, arXiv:1806.06893v1, Section II, Eq. (5) and the paragraph that
follows it. The paper defines `f_l(i) = 1` for `i <= l` and `0` otherwise, applies
the corresponding `F_l` to the prepared state, and observes that the accepted-flag
probability of the last qubit is `sum_{i <= l} p_i = P[X <= l]`. A bisection over
`l` then finds the smallest level `l_alpha` with `P[X <= l_alpha] >= 1 - alpha` in
at most `n` steps, and that level is `VaR_alpha(X)`.

This file states that chain at the source's own level: the flag probability is the
source CDF, the CDF is monotone in the threshold, the paper's VaR index is the least
crossing of the CDF against `1 - alpha`, and the exact-comparison bisection returns
precisely that index after `n` comparisons on a `2^n`-point support.

The comparisons are treated as exact. The paper obtains each CDF value from
amplitude estimation, so the statistical replacement of the comparison is a separate
question: with an explicit quantile margin the approximate readout is analysed in the
frozen `VaRQuantile` package, and `PopulationGap` records that a margin-free exact
label is not available in the finite-query model. This module asserts no accuracy
claim about approximate comparisons.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.QRiskWoerner18.PayoffMean
open scoped BigOperators

namespace Qatlib.Papers.QRiskWoerner18.VaRQuantile

/-- The source threshold payoff of Eq. (5): `f_l(i) = 1` when `i <= l` and `0` otherwise. -/
def sourceThresholdPayoff (l : ℕ) (i : ℕ) : ℝ := if i ≤ l then 1 else 0

/-- The source lower-tail mass `P[X <= l] = sum_i p_i f_l(i)` read off Eq. (5). -/
noncomputable def sourceCDF {n : ℕ} (p : FinDist (Fin (2 ^ n))) (l : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n), p.prob i * sourceThresholdPayoff l (i : ℕ)

/-- **Source Eq. (5).** For the same actual data preparation of Eq. (3), applying the
threshold payoff preparation makes the accepted-flag probability of the last qubit
equal to the lower-tail mass `P[X <= l]`. No approximate comparison is used here. -/
theorem source_threshold_flag_probability (n : ℕ) (p : FinDist (Fin (2 ^ n)))
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (l : ℕ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    MeasureProb
        (ApplyGate (payoffPreparation A (fun i => sourceThresholdPayoff l (i : ℕ)))
          (Ket (sourceZero n, false)))
        (Finset.univ.filter (fun q : Fin (2 ^ n) × Bool => q.2 = true)) = sourceCDF p l := by
  have hf : ∀ i : Fin (2 ^ n), sourceThresholdPayoff l (i : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    unfold sourceThresholdPayoff
    split <;> norm_num
  have hborn := source_born_probability n p A hcolumn
  have hflag := (payoff_actual_rotation_and_mean A (sourceZero n)
    (fun i => sourceThresholdPayoff l (i : ℕ)) hA hf).2
  rw [hflag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hborn i]

/-- The source lower-tail mass is monotone in the threshold, which is what makes the
paper's bisection invariant valid. -/
theorem sourceCDF_monotone {n : ℕ} (p : FinDist (Fin (2 ^ n))) :
    Monotone (sourceCDF p) := by
  intro l l' hll
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (p.nonneg i)
  unfold sourceThresholdPayoff
  by_cases h : (i : ℕ) ≤ l
  · rw [if_pos h, if_pos (le_trans h hll)]
  · rw [if_neg h]
    split <;> norm_num

/-- At the top of the support the source lower-tail mass is the total mass one. -/
theorem sourceCDF_at_top (n : ℕ) (p : FinDist (Fin (2 ^ n))) :
    sourceCDF p (2 ^ n - 1) = 1 := by
  have h : ∀ i : Fin (2 ^ n), sourceThresholdPayoff (2 ^ n - 1) (i : ℕ) = 1 := by
    intro i
    unfold sourceThresholdPayoff
    rw [if_pos (Nat.le_sub_one_of_lt i.isLt)]
  simp [sourceCDF, h, p.sum_one]

/-- The paper's `VaR_alpha(X)` exists: the top of the finite support always reaches the
confidence level `1 - alpha` once `alpha` is nonnegative. -/
theorem sourceVaRIndex_exists (n : ℕ) (p : FinDist (Fin (2 ^ n))) (alpha : ℝ)
    (ha : 0 ≤ alpha) : ∃ l, 1 - alpha ≤ sourceCDF p l :=
  ⟨2 ^ n - 1, by rw [sourceCDF_at_top]; linarith⟩

/-- The paper's `VaR_alpha(X)`: the smallest level `l` in the source support with
`P[X <= l] >= 1 - alpha`. -/
noncomputable def sourceVaRIndex (n : ℕ) (p : FinDist (Fin (2 ^ n))) (alpha : ℝ)
    (ha : 0 ≤ alpha) : ℕ :=
  Nat.find (sourceVaRIndex_exists n p alpha ha)

/-- **The paper's VaR characterisation.** The level returned by `sourceVaRIndex` does
reach `1 - alpha`, and every smaller level stays strictly below it, so it is exactly
the smallest value `x` with `P[X <= x] >= 1 - alpha`. -/
theorem sourceVaRIndex_spec (n : ℕ) (p : FinDist (Fin (2 ^ n))) (alpha : ℝ)
    (ha : 0 ≤ alpha) :
    1 - alpha ≤ sourceCDF p (sourceVaRIndex n p alpha ha) ∧
      ∀ l, l < sourceVaRIndex n p alpha ha → sourceCDF p l < 1 - alpha := by
  refine ⟨Nat.find_spec (sourceVaRIndex_exists n p alpha ha), fun l hl => ?_⟩
  exact not_le.mp (Nat.find_min (sourceVaRIndex_exists n p alpha ha) hl)

/-- The paper's VaR index stays inside the `2^n`-point source support. -/
theorem sourceVaRIndex_le (n : ℕ) (p : FinDist (Fin (2 ^ n))) (alpha : ℝ)
    (ha : 0 ≤ alpha) : sourceVaRIndex n p alpha ha ≤ 2 ^ n - 1 :=
  Nat.find_le (n := 2 ^ n - 1) (by rw [sourceCDF_at_top]; linarith)

/-- The exact-comparison bisection over `[lo, hi]` of Section II: one CDF comparison per
step, halving the interval each time. It returns the final lower endpoint. -/
noncomputable def sourceBisect (F : ℕ → ℝ) (q : ℝ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo then lo
      else
        let mid := (lo + hi) / 2
        if q ≤ F mid then sourceBisect F q fuel lo mid
        else sourceBisect F q fuel (mid + 1) hi

/-- Both branches keep the interval width at most half of the previous width. -/
theorem sourceBisect_width (lo hi : ℕ) (h : lo ≤ hi) :
    (lo + hi) / 2 - lo ≤ (hi - lo) / 2 ∧
      hi - ((lo + hi) / 2 + 1) ≤ (hi - lo) / 2 := by
  have hmod := Nat.div_add_mod (lo + hi) 2
  have hr : (lo + hi) % 2 ≤ 1 := by
    have := Nat.mod_lt (lo + hi) (by norm_num : 0 < 2)
    omega
  omega

/-- Halving once more keeps the width below `W` whenever it was below `2 * W`. -/
theorem sourceBisect_div_two_le {d W : ℕ} (hW : 1 ≤ W) (h : d ≤ 2 * W - 1) :
    d / 2 ≤ W - 1 := by
  have h2 : d / 2 < W := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
    omega
  omega

/-- **The bisection invariant.** If `k` is the least crossing of a monotone `F` against
`q`, every state of the exact bisection keeps the returned level between the current
lower endpoint and `k`. -/
theorem sourceBisect_bounds (F : ℕ → ℝ) (q : ℝ) (hF : Monotone F) (k : ℕ)
    (hmin : ∀ m, m < k → F m < q) (hcross : q ≤ F k) :
    ∀ (fuel lo hi : ℕ), lo ≤ k → k ≤ hi →
      lo ≤ sourceBisect F q fuel lo hi ∧ sourceBisect F q fuel lo hi ≤ k := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlk hkh
      have hb : sourceBisect F q 0 lo hi = lo := by simp [sourceBisect]
      rw [hb]
      exact ⟨le_refl _, hlk⟩
  | succ f ih =>
      intro lo hi hlk hkh
      by_cases hle : hi ≤ lo
      · have hb : sourceBisect F q (f + 1) lo hi = lo := by simp [sourceBisect, hle]
        rw [hb]
        exact ⟨le_refl _, hlk⟩
      · simp only [sourceBisect, if_neg hle]
        by_cases hq : q ≤ F ((lo + hi) / 2)
        · have hkm : k ≤ (lo + hi) / 2 := by
            by_contra hlt
            have hlt' : (lo + hi) / 2 < k := by omega
            exact absurd hq (not_le.mpr (hmin _ hlt'))
          simpa only [if_pos hq] using ih lo ((lo + hi) / 2) hlk hkm
        · have hmk : (lo + hi) / 2 + 1 ≤ k := by
            by_contra hlt
            have hlt' : k ≤ (lo + hi) / 2 := by omega
            have hle' : F k ≤ F ((lo + hi) / 2) := hF hlt'
            exact absurd (le_trans hcross hle') hq
          obtain ⟨h1, h2⟩ := ih ((lo + hi) / 2 + 1) hi hmk hkh
          simp only [if_neg hq]
          exact ⟨le_trans (by omega) h1, h2⟩

/-- **The paper's `n`-step bisection.** On a `2^n`-point support, `n` exact comparisons
suffice: the bisection returns the least crossing of a monotone `F` against `q`. -/
theorem sourceBisect_correct (F : ℕ → ℝ) (q : ℝ) (hF : Monotone F) (k : ℕ)
    (hmin : ∀ m, m < k → F m < q) (hcross : q ≤ F k) :
    ∀ (fuel lo hi : ℕ), lo ≤ k → k ≤ hi → hi - lo ≤ 2 ^ fuel - 1 →
      sourceBisect F q fuel lo hi = k := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlk hkh hw
      have hle : hi ≤ lo := by omega
      have hkl : k ≤ lo := le_trans hkh hle
      have hb : sourceBisect F q 0 lo hi = lo := by simp [sourceBisect]
      rw [hb]
      exact le_antisymm hlk hkl
  | succ f ih =>
      intro lo hi hlk hkh hw
      by_cases hle : hi ≤ lo
      · have hkl : k ≤ lo := le_trans hkh hle
        have hb : sourceBisect F q (f + 1) lo hi = lo := by simp [sourceBisect, hle]
        rw [hb]
        exact le_antisymm hlk hkl
      · have hlt : lo < hi := by omega
        have hw' : hi - lo ≤ 2 * 2 ^ f - 1 := by
          rw [mul_comm 2 (2 ^ f), ← pow_succ]; omega
        have hwidth := sourceBisect_width lo hi (le_of_lt hlt)
        simp only [sourceBisect, if_neg hle]
        by_cases hq : q ≤ F ((lo + hi) / 2)
        · have hkm : k ≤ (lo + hi) / 2 := by
            by_contra hlt'
            have hlt'' : (lo + hi) / 2 < k := by omega
            exact absurd hq (not_le.mpr (hmin _ hlt''))
          rw [if_pos hq]
          exact ih lo ((lo + hi) / 2) hlk hkm
            (le_trans hwidth.1 (sourceBisect_div_two_le (Nat.one_le_two_pow) hw'))
        · have hmk : (lo + hi) / 2 + 1 ≤ k := by
            by_contra hlt'
            have hlt'' : k ≤ (lo + hi) / 2 := by omega
            have hle' : F k ≤ F ((lo + hi) / 2) := hF hlt''
            exact absurd (le_trans hcross hle') hq
          rw [if_neg hq]
          exact ih ((lo + hi) / 2 + 1) hi hmk hkh
            (le_trans hwidth.2 (sourceBisect_div_two_le (Nat.one_le_two_pow) hw'))

/-- **Section II, VaR by bisection.** On the `2^n`-point source support, the exact
comparison bisection over `[0, 2^n - 1]` with `n` steps returns the paper's VaR index
`l_alpha`, the smallest level with `P[X <= l_alpha] >= 1 - alpha`. -/
theorem source_bisect_finds_vaR (n : ℕ) (p : FinDist (Fin (2 ^ n))) (alpha : ℝ)
    (ha : 0 ≤ alpha) :
    sourceBisect (sourceCDF p) (1 - alpha) n 0 (2 ^ n - 1) = sourceVaRIndex n p alpha ha := by
  have hspec := sourceVaRIndex_spec n p alpha ha
  exact sourceBisect_correct (sourceCDF p) (1 - alpha) (sourceCDF_monotone p)
    (sourceVaRIndex n p alpha ha) hspec.2 hspec.1 n 0 (2 ^ n - 1)
    (Nat.zero_le _) (sourceVaRIndex_le n p alpha ha) (by omega)

end Qatlib.Papers.QRiskWoerner18.VaRQuantile
