/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.AlphaFromInputQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonDiffusionAux
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.WalkFind.UniqueCollision

theorem jw_choose_removal_bound (N k s : ℕ) (hkN : k ≤ N) (hs : 0 < s) :
    Nat.choose N s ≤ Nat.choose (N - k) s + k * Nat.choose (N - 1) (s - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN' : k ≤ N := by omega
    have h := ih hkN'
    have ht : N - k = (N - (k + 1)) + 1 := by omega
    have hp := Nat.choose_succ_left (N - (k + 1)) s hs
    rw [← ht] at hp
    have hm := Nat.choose_mono (s - 1) (by omega : N - (k + 1) ≤ N - 1)
    dsimp only at hm
    calc
      _ ≤ Nat.choose (N - k) s + k * Nat.choose (N - 1) (s - 1) := h
      _ = Nat.choose (N - (k + 1)) (s - 1) + Nat.choose (N - (k + 1)) s +
          k * Nat.choose (N - 1) (s - 1) := by rw [hp]
      _ ≤ _ := by simp only [Nat.add_mul, Nat.one_mul]; omega

theorem jw_choose_avoid_half (N k s : ℕ) (hN : 0 < N) (hkN : k ≤ N)
    (hs : 0 < s) (hsize : 2 * k * s ≤ N) :
    Nat.choose N s ≤ 2 * Nat.choose (N - k) s := by
  have h := jw_choose_removal_bound N k s hkN hs
  have hmul := Nat.mul_le_mul_left N h
  have hp := Nat.add_one_mul_choose_eq (N - 1) (s - 1)
  have hn : N - 1 + 1 = N := by omega
  have hs' : s - 1 + 1 = s := by omega
  rw [hn, hs'] at hp
  have hsize' := Nat.mul_le_mul_right (Nat.choose N s) hsize
  nlinarith

theorem jwStart_zero_population_half (k N r : ℕ) (hN : 0 < N)
    (hkr : k ≤ r) (hkNr : k ≤ N - r) (hrN : r ≤ N)
    (hsize : 2 * k * (r + 1) ≤ N) :
    jwStartNormSq k N r ≤ 2 * (jwCnt k N r 0 false : ℝ) := by
  have hhalf := jw_choose_avoid_half N k (r + 1) hN (by omega) (by omega) hsize
  have hpop := jwCnt_inserted_false k N r 0 (by omega) (by omega) hkNr
  have htotal := Nat.choose_succ_right_eq N r
  rw [jwStartNormSq_eq k N r hkr hkNr hrN, hpop]
  simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.one_mul]
  have hnat : Nat.choose N r * (N - r) ≤
      2 * (Nat.choose (N - k) (r + 1) * (r + 1)) := by
    rw [← htotal]
    nlinarith
  exact_mod_cast hnat

end Qatlib.Concepts.WalkFind.WalkSpectrum
