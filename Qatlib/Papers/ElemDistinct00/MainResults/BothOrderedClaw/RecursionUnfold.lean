/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Unfolding ordered claw cost recurrences

This module defines the stopping depth of iteration of a size reduction map `r` and telescopes a
cost recurrence with square root ratios. It bounds the cost by the base cost times `sqrt N` and
an exponential in the stopping depth. A supplied comparison of that depth with `logStar` gives
the bound `logStarBound`.

The mathematical setting follows [BuhrmanEtAl2005].

## Main statements

* `telescope`: the cost recurrence unfolded through an arbitrary valid depth.
* `recursion_bound`: the bound at the least stopping depth.
* `recursion_bound_logStar`: a bound using a supplied iterated logarithm depth estimate.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw

/-- The expression `sqrt N * c^(logStar N)` for ordered claw recurrence bounds. -/
def logStarBound (c : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (N : ℝ) * c ^ logStar N

/-- For nonnegative `a` and positive `b`, the product `sqrt (a / b) * sqrt b` equals `sqrt a`. -/
theorem sqrt_div_mul_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt b = Real.sqrt a := by
  rw [← Real.sqrt_mul (div_nonneg ha hb.le)]
  congr 1
  field_simp

/-- For nonnegative `a` and positive `b` and `c`, the product `sqrt (a / b) * sqrt (b / c)`
equals `sqrt (a / c)`. -/
theorem sqrt_div_mul_sqrt_div {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a / b) * Real.sqrt (b / c) = Real.sqrt (a / c) := by
  rw [← Real.sqrt_mul (div_nonneg ha hb.le)]
  congr 1
  field_simp

/-- The result of applying the size reduction map `r` exactly `k` times to `N`. -/
def iterR (r : ℕ → ℕ) (k N : ℕ) : ℕ := (r^[k]) N

/-- If `r` maps every number greater than one to a positive smaller number, iteration from any
`N` eventually reaches a value at most one. See [Buhrman et al., 2005, Theorem
7][BuhrmanEtAl2005]. -/
theorem exists_iterR_le_one (r : ℕ → ℕ) (hr : ∀ N, 1 < N → 1 ≤ r N)
    (hrlt : ∀ N, 1 < N → r N < N) :
    ∀ N, ∃ k, iterR r k N ≤ 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 1 with hN | hN
    · exact ⟨0, by simp [iterR, Nat.le_of_lt hN]⟩
    rcases Nat.lt_or_eq_of_le hN with hN1 | hN1
    · obtain ⟨k, hk⟩ := ih (r N) (hrlt N hN1)
      refine ⟨k + 1, ?_⟩
      rw [iterR, Function.iterate_succ_apply]
      exact hk
    · exact ⟨0, by rw [← hN1]; simp [iterR]⟩

/-- The least number of iterations of a positive decreasing size reduction map needed to reach a
value at most one. -/
def depth (r : ℕ → ℕ) (hr : ∀ N, 1 < N → 1 ≤ r N)
    (hrlt : ∀ N, 1 < N → r N < N) (N : ℕ) : ℕ :=
  Nat.find (exists_iterR_le_one r hr hrlt N)

/-- Iteration at the stopping depth reaches a value at most one. -/
theorem depth_spec (r : ℕ → ℕ) (hr : ∀ N, 1 < N → 1 ≤ r N)
    (hrlt : ∀ N, 1 < N → r N < N) (N : ℕ) :
    iterR r (depth r hr hrlt N) N ≤ 1 :=
  Nat.find_spec (exists_iterR_le_one r hr hrlt N)

/-- Any iteration count that reaches a value at most one is at least the stopping depth. -/
theorem depth_min (r : ℕ → ℕ) (hr : ∀ N, 1 < N → 1 ≤ r N)
    (hrlt : ∀ N, 1 < N → r N < N) {N k : ℕ} (h : iterR r k N ≤ 1) :
    depth r hr hrlt N ≤ k :=
  Nat.find_min' (exists_iterR_le_one r hr hrlt N) h

/-- Under the stated positivity and recurrence hypotheses, unfolding `d` steps bounds `T N` by
`a^d * sqrt (N / iterR r d N) * T (iterR r d N)` while the preceding sizes exceed one. See
[Buhrman et al., 2005, Theorem 7][BuhrmanEtAl2005]. -/
theorem telescope (r : ℕ → ℕ) (T : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hr : ∀ N, 1 < N → 1 ≤ r N)
    (hrpos : ∀ N, 1 < N → 0 < r N)
    (hstep : ∀ N, 1 < N → T N ≤ a * Real.sqrt ((N : ℝ) / (r N : ℝ)) * T (r N)) :
    ∀ d N, 1 ≤ N → (∀ i, i < d → 1 < iterR r i N) →
      T N ≤ a ^ d * Real.sqrt ((N : ℝ) / (iterR r d N : ℝ)) * T (iterR r d N) := by
  intro d
  induction d with
  | zero =>
    intro N hN _
    simp only [iterR, Function.iterate_zero, id_eq, pow_zero]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [div_self hN0, Real.sqrt_one]
    simp
  | succ d ih =>
    intro N hN hchain
    have hN1 : 1 < N := by
      have := hchain 0 (Nat.zero_lt_succ d)
      simpa [iterR] using this
    have hrN1 : 1 ≤ r N := hr N hN1
    have hchain' : ∀ i, i < d → 1 < iterR r i (r N) := by
      intro i hi
      have hiter : iterR r (i + 1) N = iterR r i (r N) := by
        simp [iterR, Function.iterate_succ_apply]
      have h := hchain (i + 1) (Nat.succ_lt_succ hi)
      rwa [hiter] at h
    have hih := ih (r N) hrN1 hchain'
    have hfrac : Real.sqrt ((N : ℝ) / (r N : ℝ))
        * Real.sqrt ((r N : ℝ) / (iterR r d (r N) : ℝ))
        = Real.sqrt ((N : ℝ) / (iterR r d (r N) : ℝ)) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hr0 : (0 : ℝ) < (r N : ℝ) := by exact_mod_cast hrpos N hN1
      have hNd1 : 1 ≤ iterR r d (r N) := by
        by_cases hd0 : d = 0
        · subst hd0
          simpa [iterR] using hrN1
        · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
          rw [iterR, Function.iterate_succ_apply']
          exact hr _ (hchain' d' (Nat.lt_succ_self d'))
      have hc0 : (0 : ℝ) < (iterR r d (r N) : ℝ) := by
        exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hNd1)
      exact sqrt_div_mul_sqrt_div hN0 hr0 hc0
    have hiter : iterR r (d + 1) N = iterR r d (r N) := by
      simp [iterR, Function.iterate_succ_apply]
    calc T N
        ≤ a * Real.sqrt ((N : ℝ) / (r N : ℝ)) * T (r N) := hstep N hN1
      _ ≤ a * Real.sqrt ((N : ℝ) / (r N : ℝ))
            * (a ^ d * Real.sqrt ((r N : ℝ) / (iterR r d (r N) : ℝ))
              * T (iterR r d (r N))) := by
          apply mul_le_mul_of_nonneg_left hih
          exact mul_nonneg ha (Real.sqrt_nonneg _)
      _ = a ^ (d + 1) * Real.sqrt ((N : ℝ) / (iterR r (d + 1) N : ℝ))
            * T (iterR r (d + 1) N) := by
          rw [hiter]
          have hgroup : a * Real.sqrt ((N : ℝ) / (r N : ℝ))
              * (a ^ d * Real.sqrt ((r N : ℝ) / (iterR r d (r N) : ℝ))
                * T (iterR r d (r N)))
              = a ^ (d + 1)
                * (Real.sqrt ((N : ℝ) / (r N : ℝ))
                  * Real.sqrt ((r N : ℝ) / (iterR r d (r N) : ℝ)))
                * T (iterR r d (r N)) := by ring
          rw [hgroup, hfrac]

/-- For a nonnegative cost satisfying the stated recurrence and base bound, the cost at positive
`N` is at most `a^(depth r hr hrlt N) * sqrt N * b`. See [Buhrman et al., 2005, Theorem
7][BuhrmanEtAl2005]. -/
theorem recursion_bound (r : ℕ → ℕ) (T : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : ∀ N, 0 ≤ T N)
    (hr : ∀ N, 1 < N → 1 ≤ r N) (hrpos : ∀ N, 1 < N → 0 < r N)
    (hrlt : ∀ N, 1 < N → r N < N)
    (hstep : ∀ N, 1 < N → T N ≤ a * Real.sqrt ((N : ℝ) / (r N : ℝ)) * T (r N))
    (hbase : ∀ N, N ≤ 1 → T N ≤ b) :
    ∀ N, 1 ≤ N → T N ≤ a ^ depth r hr hrlt N * Real.sqrt (N : ℝ) * b := by
  intro N hN
  set d := depth r hr hrlt N with hd
  have hchain : ∀ i, i < d → 1 < iterR r i N := by
    intro i hi
    by_contra hle
    push Not at hle
    have hspec : iterR r i N ≤ 1 := hle
    have := depth_min r hr hrlt hspec
    omega
  have htel := telescope r T a ha hr hrpos hstep d N hN hchain
  have hd1 : 1 ≤ iterR r d N := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [hd0]
      simpa [iterR] using hN
    · have hd_eq : d = (d - 1) + 1 := (Nat.succ_pred_eq_of_pos hdpos).symm
      rw [hd_eq, iterR, Function.iterate_succ_apply']
      exact hr _ (hchain (d - 1) (by omega))
  have hspec : iterR r d N ≤ 1 := depth_spec r hr hrlt N
  have hbase' : T (iterR r d N) ≤ b := hbase _ hspec
  have hsqrt_le : Real.sqrt ((N : ℝ) / (iterR r d N : ℝ)) ≤ Real.sqrt (N : ℝ) := by
    apply Real.sqrt_le_sqrt
    have hd1r : (1 : ℝ) ≤ (iterR r d N : ℝ) := by exact_mod_cast hd1
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (iterR r d N : ℝ))]
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]
  calc T N
      ≤ a ^ d * Real.sqrt ((N : ℝ) / (iterR r d N : ℝ)) * T (iterR r d N) := htel
    _ ≤ a ^ d * Real.sqrt ((N : ℝ) / (iterR r d N : ℝ)) * b := by
        apply mul_le_mul_of_nonneg_left hbase'
        exact mul_nonneg (pow_nonneg ha d) (Real.sqrt_nonneg _)
    _ ≤ a ^ d * Real.sqrt (N : ℝ) * b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_left hsqrt_le (pow_nonneg ha d)

/-- If `1 ≤ a ≤ c` and the stopping depth is at most `logStar N`, the stated recurrence and base
bound imply `T N ≤ logStarBound c N * b`. See [Buhrman et al., 2005, Theorem
7][BuhrmanEtAl2005]. -/
theorem recursion_bound_logStar (r : ℕ → ℕ) (T : ℕ → ℝ) (a b c : ℝ)
    (ha1 : 1 ≤ a) (hb : 0 ≤ b) (hT : ∀ N, 0 ≤ T N)
    (hr : ∀ N, 1 < N → 1 ≤ r N) (hrpos : ∀ N, 1 < N → 0 < r N)
    (hrlt : ∀ N, 1 < N → r N < N)
    (hstep : ∀ N, 1 < N → T N ≤ a * Real.sqrt ((N : ℝ) / (r N : ℝ)) * T (r N))
    (hbase : ∀ N, N ≤ 1 → T N ≤ b)
    (hac : a ≤ c) {N : ℕ} (hN : 1 ≤ N)
    (hdepth : depth r hr hrlt N ≤ logStar N) :
    T N ≤ logStarBound c N * b := by
  have ha : (0 : ℝ) ≤ a := le_trans zero_le_one ha1
  have hbound := recursion_bound r T a b ha hb hT hr hrpos hrlt hstep hbase N hN
  have hpow : a ^ depth r hr hrlt N ≤ c ^ logStar N := by
    calc a ^ depth r hr hrlt N ≤ a ^ logStar N := pow_le_pow_right₀ ha1 hdepth
      _ ≤ c ^ logStar N := pow_le_pow_left₀ ha hac _
  calc T N
      ≤ a ^ depth r hr hrlt N * Real.sqrt (N : ℝ) * b := hbound
    _ ≤ c ^ logStar N * Real.sqrt (N : ℝ) * b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
    _ = logStarBound c N * b := by
        rw [logStarBound]
        ring

end Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw
