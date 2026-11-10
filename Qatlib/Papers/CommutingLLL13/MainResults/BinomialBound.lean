/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Qatlib.Papers.CommutingLLL13.MainResults.BinomialBound

theorem choose_ratio (N t : ℕ) (hN : 1 ≤ N) :
    N * (N - 1).choose t = (N - t) * N.choose t := by
  have h1 : N.choose (t + 1) * (t + 1) = N.choose t * (N - t) :=
    Nat.choose_succ_right_eq N t
  have h2 : N * (N - 1).choose t = N.choose (t + 1) * (t + 1) := by
    have := Nat.add_one_mul_choose_eq (N - 1) t
    rwa [Nat.sub_add_cancel hN] at this
  rw [h2, h1]
  ring

theorem choose_add_mul_le (m g t : ℕ) (hg : 2 ≤ g) (ht : 1 ≤ t) :
    (m + g * t).choose t ≤ 2 ^ m * (g * t).choose t := by
  induction m with
  | zero => simp
  | succ m ih =>

    have hNm1 : (m + 1) + g * t - 1 = m + g * t := by omega
    have hratio := choose_ratio ((m + 1) + g * t) t (by omega)
    rw [hNm1] at hratio

    have hle : (((m + 1) + g * t) - t) * ((m + 1) + g * t).choose t
        ≤ ((m + 1) + g * t) * (2 ^ m * (g * t).choose t) := by
      rw [← hratio]
      exact Nat.mul_le_mul_left _ ih

    have htle : t ≤ g * t := Nat.le_mul_of_pos_left t (by omega)
    have hpos : 0 < ((m + 1) + g * t) - t := by omega
    have h2t : t + t ≤ (m + 1) + g * t := by
      have h2g : 2 * t ≤ g * t := Nat.mul_le_mul_right t hg
      have htwo : t + t = 2 * t := by ring
      rw [htwo]
      exact le_trans h2g (Nat.le_add_left (g * t) (m + 1))
    have hNle : ((m + 1) + g * t) ≤ 2 * (((m + 1) + g * t) - t) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    have hstep : (((m + 1) + g * t) - t) * ((m + 1) + g * t).choose t
        ≤ (((m + 1) + g * t) - t) * (2 ^ (m + 1) * (g * t).choose t) := by
      calc (((m + 1) + g * t) - t) * ((m + 1) + g * t).choose t
          ≤ ((m + 1) + g * t) * (2 ^ m * (g * t).choose t) := hle
        _ ≤ (2 * (((m + 1) + g * t) - t)) * (2 ^ m * (g * t).choose t) :=
            Nat.mul_le_mul_right _ hNle
        _ = (((m + 1) + g * t) - t) * (2 ^ (m + 1) * (g * t).choose t) := by
            rw [Nat.pow_succ]
            ac_rfl
    exact Nat.le_of_mul_le_mul_left hstep hpos

end Qatlib.Papers.CommutingLLL13.MainResults.BinomialBound
