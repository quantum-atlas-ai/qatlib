/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An integrated lower bound for adiabatic search

This module proves the scalar estimates used in the optimality argument of [RolandCerf2002]. A
finite Cauchy–Schwarz bound controls a sum by its squared mass, and
`source_optimality_lower_bound` turns the stated derivative and final-distance assumptions into
a lower bound on the runtime.

## Main statements

* `sum_le_sqrt_mul_of_sum_sq`: Bounds a nonnegative sum from its sum of squares.
* `source_optimality_lower_bound`: Derives `T ≥ ε * (N - 1) / (4 * sqrt N)`.

## References

* [Roland and Cerf, 2002][RolandCerf2002]
-/

set_option autoImplicit false
noncomputable section

open Real
open MeasureTheory
open scoped Interval

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality

/-- If nonnegative entries have sum of squares `s^2` with `s ≥ 0`, their sum is at most `sqrt N
* s` [RolandCerf2002]. -/
theorem sum_le_sqrt_mul_of_sum_sq {N : ℕ} {s : ℝ} (u : Fin N → ℝ)
    (hu : ∀ m, 0 ≤ u m) (hs : 0 ≤ s)
    (h : ∑ m, (u m) ^ 2 = s ^ 2) :
    ∑ m, u m ≤ sqrt N * s := by
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hcs : (∑ m, u m) ^ 2 ≤ (N : ℝ) * s ^ 2 := by
    have hbase := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := u)
    simpa [h] using hbase
  have hsum_nonneg : 0 ≤ ∑ m, u m := Finset.sum_nonneg (fun m _ => hu m)
  have hright_nonneg : 0 ≤ sqrt N * s := mul_nonneg (sqrt_nonneg N) hs
  have hsq : (∑ m, u m) ^ 2 ≤ (sqrt N * s) ^ 2 := by
    rw [mul_pow, sq_sqrt hNnonneg]
    exact hcs
  exact (sq_le_sq₀ hsum_nonneg hright_nonneg).mp hsq

/-- For `N ≥ 2`, the stated derivative bound, schedule upper bound, and final-distance lower
bound imply `T ≥ ε * (N - 1) / (4 * sqrt N)`, as in the optimality argument of
[RolandCerf2002]. -/
theorem source_optimality_lower_bound
    (N : ℕ) (ε T : ℝ) (s f A : ℝ → ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hT : 0 ≤ T)
    (hs1 : ∀ t, s t ≤ 1)
    (hA0 : A 0 = 0)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt A (f t) t)
    (hfcont : Continuous f)
    (hfle : ∀ t, f t ≤ 4 * (N : ℝ) * sqrt N * s t)
    (hdist : ε * ((N : ℝ) * ((N : ℝ) - 1)) ≤ A T) :
    T ≥ ε * ((N : ℝ) - 1) / (4 * sqrt N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcnonneg : (0 : ℝ) ≤ 4 * (N : ℝ) * sqrt N := by positivity
  have hfint : IntervalIntegrable f volume (0 : ℝ) T := hfcont.intervalIntegrable 0 T

  have hfconst : ∀ t, f t ≤ 4 * (N : ℝ) * sqrt N := by
    intro t
    have h1 := hfle t
    have h2 := hs1 t
    nlinarith [h1, h2, hcnonneg]

  have hFTC : ∫ t in (0 : ℝ)..T, f t = A T - A 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := T) hderiv hfint

  have hbound : ∫ t in (0 : ℝ)..T, f t ≤ 4 * (N : ℝ) * sqrt N * T := by
    have hm : ∫ t in (0 : ℝ)..T, f t ≤ ∫ t in (0 : ℝ)..T, (4 * (N : ℝ) * sqrt N) :=
      intervalIntegral.integral_mono_on (f := f) (g := fun _ => 4 * (N : ℝ) * sqrt N)
        (hab := hT) (hf := hfint)
        (hg := continuous_const.intervalIntegrable (0 : ℝ) T)
        (h := fun x _ => hfconst x)
    have hc : ∫ t in (0 : ℝ)..T, (4 * (N : ℝ) * sqrt N) = 4 * (N : ℝ) * sqrt N * T := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      ring
    calc ∫ t in (0 : ℝ)..T, f t
        ≤ ∫ t in (0 : ℝ)..T, (4 * (N : ℝ) * sqrt N) := hm
      _ = 4 * (N : ℝ) * sqrt N * T := hc

  have hAT : A T ≤ 4 * (N : ℝ) * sqrt N * T := by
    have hEq : ∫ t in (0 : ℝ)..T, f t = A T := by
      rw [hFTC, hA0, sub_zero]
    rw [← hEq]
    exact hbound

  have hkey : ε * ((N : ℝ) - 1) ≤ 4 * sqrt N * T := by
    have hmul : (N : ℝ) * (ε * ((N : ℝ) - 1)) ≤ (N : ℝ) * (4 * sqrt N * T) := by
      nlinarith [hdist, hAT]
    exact (mul_le_mul_iff_of_pos_left hNpos).mp hmul
  have h4 : 0 < 4 * sqrt N := by positivity
  change ε * ((N : ℝ) - 1) / (4 * sqrt N) ≤ T
  rw [div_le_iff₀ h4]
  nlinarith [hkey]

end Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality
