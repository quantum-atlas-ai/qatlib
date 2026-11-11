/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Uniform sampling for perceptron mistakes

Bounds the probability of missing a nonempty set of misclassified examples under independent
uniform sampling. The concrete ceiling budget, its margin-dependent specialization, and the
zero-mistake convention formalize Lemma 1 of [WiebeKapoorSvore2016].

## Main statements

* `source_lemma1_failure_bound`: For every `m ≤ N`, the prescribed uniform sample count bounds
  `samplingFailure` by `δ`, including the zero-marked convention [WiebeKapoorSvore2016].
* `source_lemma1_query_count_linear`: For `0 < δ ≤ 1 / 2`, the ceiling sample budget is at most
  `3 * N * log (1 / δ)`.

## References

* [Wiebe et al., 2016][WiebeKapoorSvore2016]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPerceptron16.UniformSample

open scoped BigOperators

/-- The single-draw probability expression `(N - m) / N` for missing `m` marked examples among
`N` examples. -/
def missProbability (N m : ℕ) : ℝ := ((N : ℝ) - (m : ℝ)) / (N : ℝ)

/-- When `N` is positive and `m ≤ N`, the single-draw miss probability is nonnegative. -/
theorem missProbability_nonneg {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) :
    0 ≤ missProbability N m := by
  unfold missProbability
  apply div_nonneg
  · have hm' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
    linarith
  · positivity

/-- If `N` is positive and at least one example is marked, the miss probability is at most `1 -
1 / N`. -/
theorem missProbability_le_one_sub_inv {N m : ℕ} (hN : 0 < N) (hm : 1 ≤ m) :
    missProbability N m ≤ 1 - 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold missProbability
  rw [div_le_iff₀ hNpos]
  have hrhs : (1 - 1 / (N : ℝ)) * (N : ℝ) = (N : ℝ) - 1 := by
    field_simp
  rw [hrhs]
  linarith

/-- For `1 ≤ m ≤ N`, the probability expression for `k` independent misses is at most `exp (-k /
N)`. -/
theorem missProbability_pow_le_exp {N m k : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    missProbability N m ^ k ≤ Real.exp (-(k : ℝ) / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnn : 0 ≤ missProbability N m := missProbability_nonneg hN hmN
  have hle := missProbability_le_one_sub_inv (N := N) (m := m) hN hm
  have hexp : (1 : ℝ) - 1 / (N : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) :=
    Real.one_sub_le_exp_neg (1 / (N : ℝ))
  have hbase : missProbability N m ≤ Real.exp (-(1 / (N : ℝ))) := hle.trans hexp
  calc missProbability N m ^ k
      ≤ (Real.exp (-(1 / (N : ℝ)))) ^ k := pow_le_pow_left₀ hnn hbase k
    _ = Real.exp ((k : ℝ) * (-(1 / (N : ℝ)))) := by
          rw [Real.exp_nat_mul]
    _ = Real.exp (-(k : ℝ) / (N : ℝ)) := by
          congr 1
          field_simp

/-- For `1 ≤ m ≤ N`, a sample count of `ceil (N * log (1 / δ))` makes the miss probability at
most `δ` [WiebeKapoorSvore2016]. -/
theorem source_lemma1_query_bound
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) :
    ∀ m : ℕ, 1 ≤ m → m ≤ N →
      missProbability N m ^ (Nat.ceil ((N : ℝ) * Real.log (1 / δ))) ≤ δ := by
  intro m hm hmN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow := missProbability_pow_le_exp (N := N) (m := m)
    (k := Nat.ceil ((N : ℝ) * Real.log (1 / δ))) hN hm hmN
  have hceil : (N : ℝ) * Real.log (1 / δ)
      ≤ ((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ) := Nat.le_ceil _
  have hquot : Real.log (1 / δ)
      ≤ ((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos]
    linarith
  have hmono : Real.exp (-(((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ) / (N : ℝ)))
      ≤ Real.exp (-(Real.log (1 / δ))) := by
    apply Real.exp_le_exp_of_le
    linarith
  have hlog1 : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  have hexpδ : Real.exp (-(Real.log (1 / δ))) = δ := by
    rw [hlog1, neg_neg, Real.exp_log hδ0]
  have hpow' : missProbability N m ^ (Nat.ceil ((N : ℝ) * Real.log (1 / δ)))
      ≤ Real.exp (-(((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ) / (N : ℝ))) := by
    simpa only [neg_div] using hpow
  calc missProbability N m ^ (Nat.ceil ((N : ℝ) * Real.log (1 / δ)))
      ≤ Real.exp (-(((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ) / (N : ℝ))) := hpow'
    _ ≤ Real.exp (-(Real.log (1 / δ))) := hmono
    _ = δ := hexpδ

/-- The uniform sampling budget at confidence `ε * γ^2` bounds the miss probability by `ε * γ^2`
when at least one example is marked. -/
theorem source_lemma1_eps_gamma
    (N : ℕ) (hN : 0 < N) (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (hδ : ε * γ ^ 2 ≤ 1) :
    ∀ m : ℕ, 1 ≤ m → m ≤ N →
      missProbability N m ^ (Nat.ceil ((N : ℝ) * Real.log (1 / (ε * γ ^ 2)))) ≤ ε * γ ^ 2 := by
  have hδ0 : 0 < ε * γ ^ 2 := by positivity
  exact source_lemma1_query_bound N hN (ε * γ ^ 2) hδ0 hδ

/-- The sampling failure expression, defined to be zero when no example is marked and otherwise
the independent miss probability. -/
def samplingFailure (N m k : ℕ) : ℝ := if m = 0 then 0 else missProbability N m ^ k

/-- For every `m ≤ N`, the prescribed uniform sample count bounds `samplingFailure` by `δ`,
including the zero-marked convention [WiebeKapoorSvore2016]. -/
theorem source_lemma1_failure_bound
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ m : ℕ, m ≤ N →
      samplingFailure N m (Nat.ceil ((N : ℝ) * Real.log (1 / δ))) ≤ δ := by
  intro m hmN
  by_cases hm0 : m = 0
  · simp [samplingFailure, hm0, hδ0.le]
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    simpa [samplingFailure, hm0] using source_lemma1_query_bound N hN δ hδ0 hδ1 m hm hmN

/-- For `0 < δ ≤ 1 / 2`, the ceiling sample budget is at most `3 * N * log (1 / δ)`. -/
theorem source_lemma1_query_count_linear
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ)
      ≤ 3 * (N : ℝ) * Real.log (1 / δ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlog2 : Real.log 2 ≤ Real.log (1 / δ) := by
    rw [Real.log_le_log_iff (by norm_num) (by positivity)]
    rw [le_div_iff₀ hδ0]
    nlinarith [hδ1]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 1 / 2 ≤ (N : ℝ) * Real.log (1 / δ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h0N : (0 : ℝ) ≤ (N : ℝ) := by linarith
    have hmul : 1 * Real.log 2 ≤ (N : ℝ) * Real.log (1 / δ) :=
      mul_le_mul hN1 hlog2 hlog2pos.le h0N
    have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hxpos : (0 : ℝ) < (N : ℝ) * Real.log (1 / δ) := by linarith
  have hceil := Nat.ceil_lt_add_one (le_of_lt hxpos)
  calc ((Nat.ceil ((N : ℝ) * Real.log (1 / δ))) : ℝ)
      ≤ (N : ℝ) * Real.log (1 / δ) + 1 := le_of_lt hceil
    _ ≤ 3 * ((N : ℝ) * Real.log (1 / δ)) := by linarith
    _ = 3 * (N : ℝ) * Real.log (1 / δ) := by ring

end Qatlib.Papers.QPerceptron16.UniformSample
