/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

theorem iterLog_succ (k : ℕ) (x : ℝ) : iterLog (k + 1) x = Real.log (iterLog k x) :=
  rfl

theorem iterLog_le_sub (N : ℕ) (k : ℕ)
    (hchain : ∀ j ≤ k, 1 < iterLog j (N : ℝ)) :
    iterLog k (N : ℝ) ≤ (N : ℝ) - (k : ℝ) := by
  induction k with
  | zero =>
      simp [iterLog]
  | succ k ih =>
      have hk : ∀ j ≤ k, 1 < iterLog j (N : ℝ) :=
        fun j hj => hchain j (Nat.le_succ_of_le hj)
      have hkle : iterLog k (N : ℝ) ≤ (N : ℝ) - (k : ℝ) := ih hk
      have h1 : 1 < iterLog k (N : ℝ) := hchain k (Nat.le_succ k)
      have hlog : Real.log (iterLog k (N : ℝ)) ≤ iterLog k (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (lt_trans zero_lt_one h1)
      have hstep : iterLog (Nat.succ k) (N : ℝ) ≤ (N : ℝ) - (k : ℝ) - 1 := by
        rw [show Nat.succ k = k + 1 from rfl, iterLog_succ]
        linarith
      have hcast : (N : ℝ) - (k : ℝ) - 1 = (N : ℝ) - ((Nat.succ k : ℕ) : ℝ) := by
        push_cast
        ring
      linarith

theorem exists_iterLog_le_one (N : ℕ) : ∃ k, iterLog k (N : ℝ) ≤ 1 := by
  by_contra h
  push Not at h
  have hle := iterLog_le_sub N N (fun j _ => h j)
  have hpos : 0 < iterLog N (N : ℝ) := lt_trans zero_lt_one (h N)
  have hnonpos : iterLog N (N : ℝ) ≤ 0 := by
    simpa using hle
  linarith

noncomputable def logStar (N : ℕ) : ℕ :=
  Nat.find (exists_iterLog_le_one N)

theorem logStar_spec (N : ℕ) : iterLog (logStar N) (N : ℝ) ≤ 1 :=
  Nat.find_spec (exists_iterLog_le_one N)

theorem logStar_min {N k : ℕ} (h : iterLog k (N : ℝ) ≤ 1) : logStar N ≤ k :=
  Nat.find_min' (exists_iterLog_le_one N) h

end Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw
