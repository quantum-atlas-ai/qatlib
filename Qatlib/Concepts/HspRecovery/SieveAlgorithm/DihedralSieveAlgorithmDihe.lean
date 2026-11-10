/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm

open Qatlib

private theorem clause5_readout_hit (n : ℕ) (s : ZMod (2 ^ n)) (L : List (ZMod (2 ^ n))) :
    idealReadout n s L (some (decide (s.val % 2 = 1)))
      = if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 1 else 0 := by
  classical
  rw [idealReadout]
  cases hF : L.find? (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none =>
      have hnm : ¬((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L := by
        intro hmem
        exact absurd (List.find?_eq_none (p := fun r =>
          decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))).1 hF _ hmem) (by simp)
      show (PMF.pure (none : Option Bool)) (some (decide (s.val % 2 = 1)))
          = if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 1 else 0
      rw [PMF.pure_apply, if_neg (by simp), if_neg hnm]
  | some r =>
      have hr : r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) :=
        of_decide_eq_true (List.find?_some (p := fun x =>
          decide (x = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) hF)
      have hmem : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L := by
        have hrm := List.mem_of_find?_eq_some hF
        rwa [hr] at hrm
      show (parityReadout (dihedralQubitState (2 ^ n) s r)
          (normalized_dihedralQubitState (2 ^ n) s r)).map some
          (some (decide (s.val % 2 = 1)))
          = if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L then 1 else 0
      rw [hr, dihedralParityReadoutPure, PMF.pure_map, PMF.pure_apply, if_pos hmem]
      simp

private theorem clause5_run_success_eq_hit (n m : ℕ) (s : ZMod (2 ^ n)) :
    (dihedralSieveRun n m s).1 (some (decide (s.val % 2 = 1)))
      = ∑' L : List (ZMod (2 ^ n)),
        if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
          then ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L
          else 0 := by
  show (((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)).bind
      (idealReadout n s)) (some (decide (s.val % 2 = 1))) = _
  rw [PMF.bind_apply]
  refine tsum_congr fun L => ?_
  rw [clause5_readout_hit n s L]
  by_cases hL : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
  · rw [if_pos hL, if_pos hL, mul_one]
  · rw [if_neg hL, if_neg hL, mul_zero]

theorem dihedralSieveAlgorithm : DihedralSieveAlgorithm := by
  intro n hn S _ _ _ f s hf
  refine ⟨fun b hb =>
      dihedralSieveWrongAnswerZero n (Nat.ceil (Real.sqrt (n - 1))) s b hb,
    ?_, dihedralSieveBudget n (Nat.ceil (Real.sqrt (n - 1))) s⟩
  rw [clause5_run_success_eq_hit n (Nat.ceil (Real.sqrt (n - 1))) s]
  refine le_trans ?_
    (dihedralSieveIdealHit n (Nat.ceil (Real.sqrt (n - 1))) hn rfl)
  exact ENNReal.ofReal_le_ofReal
    (sub_le_self _ (Real.rpow_pos_of_pos (by norm_num) _).le)

end Qatlib.Concepts.HspRecovery.SieveAlgorithm
