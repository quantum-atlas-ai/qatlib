/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Th5NumericPolylogStat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.CorrectedWalkBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem least_power_numeric_charge (n k r qH Q : ℕ) (hn : 0 < n) (hk : 4 ≤ k)
    (hr : 1 ≤ r) (hl : n ^ (k - 1) ≤ r ^ k)
    (hu : (r - 1) ^ k < n ^ (k - 1)) (hq : qH ≤ Q) :
    (((r * r + (n / r) ^ ((k - 1) / 2) * (qH + Nat.sqrt r * r) : ℕ)) : ℝ) ≤
      (4 + (Q : ℝ) + 4) * (n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  let α : ℝ := ((k : ℝ) - 1) / k
  let a : ℝ := (n : ℝ) ^ α
  let b : ℝ := (n : ℝ) ^ (1 / (k : ℝ))
  let t : ℝ := (n : ℝ) ^ (α / 2)
  have hα : 0 ≤ α := by
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg (by linarith) hkR.le
  have ha : 0 < a := Real.rpow_pos_of_pos hnR _
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 hα
  have hb : 0 < b := Real.rpow_pos_of_pos hnR _
  have ht : 0 < t := Real.rpow_pos_of_pos hnR _
  have ht1 : 1 ≤ t := Real.one_le_rpow hn1 (by positivity)
  have haK : a ^ k = (n : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    dsimp [a, α]
    rw [div_mul_cancel₀ _ hkR.ne', ← hkm, Real.rpow_natCast]
  have har : a ≤ (r : ℝ) := by
    apply (pow_le_pow_iff_left₀ ha.le (Nat.cast_nonneg r) (by omega : k ≠ 0)).mp
    rw [haK]
    exact_mod_cast hl
  have hra : (r : ℝ) ≤ 2 * a := by
    have hx : ((r - 1 : ℕ) : ℝ) ≤ a := by
      apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) ha.le (by omega : k ≠ 0)).mp
      rw [haK]
      exact_mod_cast hu.le
    rw [Nat.cast_sub hr, Nat.cast_one] at hx
    linarith
  have hab : a * b = (n : ℝ) := by
    dsimp [a, b]
    rw [← Real.rpow_add hnR]
    have he : α + 1 / (k : ℝ) = 1 := by dsimp [α]; field_simp; ring
    rw [he, Real.rpow_one]
  have hdiv : ((n / r : ℕ) : ℝ) ≤ b := by
    apply (mul_le_mul_iff_of_pos_right ha).mp
    calc
      ((n / r : ℕ) : ℝ) * a ≤ ((n / r : ℕ) : ℝ) * r :=
        mul_le_mul_of_nonneg_left har (Nat.cast_nonneg _)
      _ ≤ n := by exact_mod_cast Nat.div_mul_le_self n r
      _ = b * a := by rw [mul_comm, hab]
  have ht2 : t ^ 2 = a := by
    dsimp [t, a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    norm_num
  have hpow : (((n / r : ℕ) : ℝ) ^ ((k - 1) / 2)) ≤ t := by
    calc
      _ ≤ b ^ ((k - 1) / 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv _
      _ = (n : ℝ) ^ ((1 / (k : ℝ)) * (((k - 1) / 2 : ℕ) : ℝ)) := by
        dsimp [b]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      _ ≤ t := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have hd : (((k - 1) / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) - 1 := by
          rw [← hkm]
          exact_mod_cast Nat.div_mul_le_self (k - 1) 2
        dsimp [α]
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        apply (le_div_iff₀ hkR).mpr
        field_simp
        nlinarith
  have hs : (Nat.sqrt r : ℝ) ≤ 2 * t := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity : 0 ≤ 2 * t)).mp
    have hs2 : (Nat.sqrt r : ℝ) ^ 2 ≤ r := by exact_mod_cast Nat.sqrt_le' r
    nlinarith [ht2]
  have hr2 : (r : ℝ) ^ 2 ≤ 4 * a ^ 2 := by nlinarith [sq_nonneg (2 * a - r)]
  have hprod : (((n / r : ℕ) : ℝ) ^ ((k - 1) / 2)) *
      (Nat.sqrt r : ℝ) * r ≤ 4 * a ^ 2 := by
    have hp := mul_le_mul hpow hs (Nat.cast_nonneg _) ht.le
    have hp' := mul_le_mul hp hra (Nat.cast_nonneg _) (by positivity : 0 ≤ t * (2 * t))
    nlinarith [ht2]
  have htA : t ≤ a ^ 2 := by nlinarith [ht2, sq_nonneg (a - 1)]
  have hqR : (qH : ℝ) ≤ Q := by exact_mod_cast hq
  have hqprod : (((n / r : ℕ) : ℝ) ^ ((k - 1) / 2)) * qH ≤ (Q : ℝ) * a ^ 2 := by
    calc
      _ ≤ t * Q := mul_le_mul hpow hqR (Nat.cast_nonneg _) ht.le
      _ ≤ a ^ 2 * Q := mul_le_mul_of_nonneg_right htA (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  have ha2 : a ^ 2 = (n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ)) := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    dsimp [α]
    field_simp
  push_cast
  rw [← ha2]
  nlinarith

theorem th5NumericPolylog_answer : Th5NumericPolylog := by
  intro k hk kcs hκ Q
  refine ⟨2 * (kcs.κ : ℝ) * (4 + (Q : ℝ) + 4), by positivity, ?_⟩
  intro n hn H hv adj qH hq
  obtain ⟨r, hr, hl, hu⟩ := correctedSubsetWindow (n ^ (k - 1)) k
    (pow_pos hn _) (by omega)
  refine ⟨r, hr, hl, hu, ?_⟩
  intro stape
  have hc := kcs.charges r (hCandRel adj H hv) (r * r) r qH (stape 0)
  have hraw : (hAlg adj H hv kcs r qH stape).2 ≤
      kcs.κ * (Nat.log 2 (n + 1) + 2) *
        (r * r + (n / r) ^ ((k - 1) / 2) * (qH + Nat.sqrt r * r)) := by
    cases he : kcs.run r (hCandRel adj H hv) (r * r) r qH (stape 0) with
    | none => simpa only [hAlg, he] using hc
    | some K => simp only [hAlg, he]; split_ifs <;> exact hc
  have hnum := least_power_numeric_charge n k r qH Q hn hk hr hl hu hq
  have hlog : ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) ≤
      2 * ((Nat.log 2 n + 2 : ℕ) : ℝ) := by
    exact_mod_cast corrected_log_succ_le n hn
  have hL : (2 : ℝ) ≤ ((Nat.log 2 n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ Nat.log 2 n + 2 by omega)
  have hL3 : ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤ ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (((Nat.log 2 n + 2 : ℕ) : ℝ) - 1)]
  calc
    _ ≤ (kcs.κ : ℝ) * (((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ)) *
        (((r * r + (n / r) ^ ((k - 1) / 2) * (qH + Nat.sqrt r * r) : ℕ)) : ℝ) := by
          exact_mod_cast hraw
    _ ≤ (kcs.κ : ℝ) * (2 * ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 3) *
        ((4 + (Q : ℝ) + 4) * (n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hlog.trans (by linarith)) (Nat.cast_nonneg _))
        hnum (by positivity) (by positivity)
    _ = _ := by ring

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
