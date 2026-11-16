/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StarDecompSim10.ForestColors.ColorRefine
public import Mathlib.Order.Iterate

@[expose] public section


/-! # Full historical bit-width recurrence

Fixed actual source1003.3683v2 Lemma2. Padded widths n+3 admit a
strong induction down the actual binary logarithm. No final recurrence
bound is assumed, and every original natural input including0/1 remains.
-/

set_option autoImplicit false
namespace Qatlib.Papers.StarDecompSim10.ForestColors.WidthRounds
open Qatlib.Papers.StarDecompSim10.ForestColors

/-- The exact original bit-width recurrence. -/
def nextBits (L : ℕ) : ℕ := Nat.log2 (2*L-1)+1

/-- The natural binary logarithm is monotone, including zero. -/
theorem logMono : Monotone Nat.log2 := by
  intro a b hab
  by_cases ha : a=0
  · simp [ha]
  · have hb : b≠0 := by omega
    exact (Nat.le_log2 hb).mpr ((Nat.log2_self_le ha).trans hab)

/-- Width refinement preserves order. -/
theorem nextMono : Monotone nextBits := by
  intro a b hab
  have h := logMono (show 2*a-1 ≤ 2*b-1 by omega)
  unfold nextBits
  omega

/-- Every iterate preserves order. -/
theorem iterMono (k : ℕ) : Monotone (nextBits^[k]) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih =>
    intro a b hab
    simpa only [Function.iterate_succ_apply'] using nextMono (ih hab)

/-- The padded recurrence is dominated by a padded binary logarithm above the base cases. -/
theorem nextPadded (n : ℕ) (hn : 2 ≤ n) : nextBits (n+3) ≤ Nat.log2 n+3 := by
  have hpow := Nat.lt_log2_self (n := n)
  have he : (2 : ℕ)^(Nat.log2 n+3) = 4*2^(Nat.log2 n+1) := by
    rw [show Nat.log2 n+3=(Nat.log2 n+1)+2 by omega, pow_add]
    omega
  have hx : 2*(n+3)-1 < 2^(Nat.log2 n+3) := by
    rw [he]
    omega
  have hl := (Nat.log2_lt (by omega : 2*(n+3)-1≠0)).mpr hx
  unfold nextBits
  omega

/-- Padded width n+3 reaches at most four within the original log-star count. -/
theorem padded (n : ℕ) : (nextBits^[logStar n]) (n+3) ≤ 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [logStar]
    · simp [logStar]
    · have hn : Nat.log2 (n+2) < n+2 := by
        by_contra h
        have hge : n+2 ≤ Nat.log2 (n+2) := by omega
        have hp := (Nat.le_log2 (by omega : n+2≠0)).mp hge
        have ht := Nat.lt_two_pow_self (n := n+2)
        omega
      rw [logStar, Nat.add_comm 1, Function.iterate_succ_apply]
      exact (iterMono _ (nextPadded (n+2) (by omega))).trans (ih _ hn)

/-- The full original sharp recurrence target holds for every natural input. -/
theorem wholeOriginal (N : ℕ) : (nextBits^[logStar N]) (Nat.log2 N+1) ≤ 3 := by
  rcases N with _ | _ | N
  · simp [logStar]
  · simp [logStar]
  · have h := (iterMono (logStar (Nat.log2 (N+2)))
        (show Nat.log2 (N+2)+1 ≤ Nat.log2 (N+2)+3 by omega)).trans
        (padded (Nat.log2 (N+2)))
    rw [logStar, Nat.add_comm 1, Function.iterate_succ_apply']
    have hh := nextMono h
    simpa only [show nextBits 4=3 by decide] using hh

end Qatlib.Papers.StarDecompSim10.ForestColors.WidthRounds
