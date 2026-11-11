/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic

/-!
# The (S66) upper bound from the exact finite-pair variance identity

Fixed source: Hsin-Yuan Huang, Richard Kueng, John Preskill, *Predicting Many
Properties of a Quantum System from Very Few Measurements*, arXiv:2002.08953v2,
PDF SHA256 `7d0b0d0896354d6261fa36f3e4b5ed79c5b0334c966310d5d516e53671e0eef5`.

Source location: supplementary §6A, PDF pp. 28--29 — Lemma 5, Eqs. (S65)--(S66).

The exact variance of the pairwise U-statistic is (S65),
`Var = C(N,2)^{-1}(Var[pair] + 2(N-2)·Var[linear])`, which the frozen
`finite_pair_u_statistic_exact_variance` already proves. The first inequality
of (S66) is the elementary comparison of the two rational coefficients with the
constants `4/N²` and `4/N`:

* `4·(N-2)/(N·(N-1)) ≤ 4/N`, and
* `2/(N·(N-1)) ≤ 4/N²` (equivalently `N ≥ 2`).

This module turns that comparison into a theorem about the *actual* finite-pair
statistic, so the (S66) upper bound is a corollary of the exact identity rather
than a separately assumed estimate. The constants are the source's conservative
ones; the sharper `2/N` split over the two distinct linear-ordering terms
(Var[(A+B)/2] ≤ (Var A + Var B)/2) is a separate, observable-specific step and
is not asserted here.
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ShadowModels.UStatBackend

namespace Qatlib.Papers.ClassShadows20.ShadowVariance

open scoped BigOperators
set_option autoImplicit false

/-- The conditional kernel variance is a sum of nonnegative "prob times square"
terms, hence nonnegative. -/
theorem pairConditionalVariance_nonneg {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    0 ≤ pairConditionalVariance p h := by
  unfold pairConditionalVariance
  exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg _)

/-- The two-record kernel variance is a sum of nonnegative "prob times square"
terms, hence nonnegative. -/
theorem pairKernelVariance_nonneg {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    0 ≤ pairKernelVariance p h := by
  unfold pairKernelVariance
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (p.nonneg x) (p.nonneg y)) (sq_nonneg _)

/-- Coefficient comparison `4(N-2)/(N(N-1)) ≤ 4/N` behind the first inequality
of Eq. (S66). -/
theorem pair_linear_coefficient_le (m : ℕ) (hm : 2 ≤ m) :
    (4 * ((m - 2 : ℕ) : ℝ)) / ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) ≤ 4 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  have hden : (0 : ℝ) < (m : ℝ) * ((m - 1 : ℕ) : ℝ) := mul_pos hm0 hm1
  rw [div_le_div_iff₀ hden hm0]
  have hcast : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
  have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [hcast, hcast1]
  nlinarith

/-- Coefficient comparison `2/(N(N-1)) ≤ 4/N²` behind the pair term of
Eq. (S66). -/
theorem pair_kernel_coefficient_le (m : ℕ) (hm : 2 ≤ m) :
    2 / ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) ≤ 4 / (m : ℝ) ^ 2 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  have hden : (0 : ℝ) < (m : ℝ) * ((m - 1 : ℕ) : ℝ) := mul_pos hm0 hm1
  have hsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hsq]
  have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hcast1]
  nlinarith

/-- **Lemma 5 / Eq. (S66), first inequality, on the actual finite-pair
statistic.**  For a symmetric real kernel and at least two records, the variance
of the pairwise U-statistic is at most `4/N` times the conditional kernel
variance plus `4/N²` times the two-record kernel variance.  This is exactly the
`4/N² Var[pair] + 4/N Var[linear]` bound of (S66), obtained from the frozen
exact decomposition `finite_pair_u_statistic_exact_variance` (S65) by comparing
the rational coefficients. -/
theorem finite_pair_u_statistic_variance_le_s66
    (X : Type) [Fintype X] (p : FinDist X) (m : ℕ) (h : X → X → ℝ)
    (hm : 2 ≤ m) (hsym : ∀ x y, h x y = h y x) :
    (∑ ω : Fin m → X, p.probOf ω * (pairUStatistic h ω - pairKernelMean p h) ^ 2)
      ≤ (4 / (m : ℝ)) * pairConditionalVariance p h
        + (4 / (m : ℝ) ^ 2) * pairKernelVariance p h := by
  rw [finite_pair_u_statistic_exact_variance X p m h hm hsym]
  have hC : 0 ≤ pairConditionalVariance p h := pairConditionalVariance_nonneg p h
  have hK : 0 ≤ pairKernelVariance p h := pairKernelVariance_nonneg p h
  have h1 : (4 * ((m - 2 : ℕ) : ℝ)) / ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) *
      pairConditionalVariance p h ≤ (4 / (m : ℝ)) * pairConditionalVariance p h :=
    mul_le_mul_of_nonneg_right (pair_linear_coefficient_le m hm) hC
  have h2 : 2 / ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * pairKernelVariance p h ≤
      (4 / (m : ℝ) ^ 2) * pairKernelVariance p h :=
    mul_le_mul_of_nonneg_right (pair_kernel_coefficient_le m hm) hK
  linarith

end Qatlib.Papers.ClassShadows20.ShadowVariance
