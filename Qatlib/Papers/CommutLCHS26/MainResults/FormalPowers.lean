/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers

open scoped BigOperators

variable {A : Type} [Ring A]

theorem power_coeff_vanish (f : PowerSeries A) (hf : f.constantCoeff = 0)
    (n j : ℕ) (hj : n < j) : PowerSeries.coeff n (f ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hj)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j hf)

theorem power_coefficient_newton (f : PowerSeries A) (hf : f.constantCoeff = 1) (n q : ℕ) :
    PowerSeries.coeff n (f ^ q) =
      ∑ j ∈ Finset.range (n + 1), q.choose j • PowerSeries.coeff n ((f - 1) ^ j) := by
  have hz : (f - 1).constantCoeff = 0 := by simp [hf]
  have hp : f ^ q = ∑ j ∈ Finset.range (q + 1), q.choose j • (f - 1) ^ j := by
    calc
      _ = ((f - 1) + 1) ^ q := by rw [sub_add_cancel]
      _ = _ := by
        rw [(Commute.one_right (f - 1)).add_pow q]
        simp only [one_pow, mul_one, nsmul_eq_mul']
  rw [hp, map_sum]
  simp only [map_nsmul]
  rcases le_total q n with h | h
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    have hjq : q < j := by simp only [Finset.mem_range] at hj'; omega
    simp [Nat.choose_eq_zero_of_lt hjq]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    have hjn : n < j := by simp only [Finset.mem_range] at hj'; omega
    simp [power_coeff_vanish (f - 1) hz n j hjn]

end Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers
