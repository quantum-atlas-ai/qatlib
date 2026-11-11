/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Iterated logarithms for ordered claw finding

This module defines natural logarithm iteration `iterLog` and the stopping index `logStar`. It
proves that the iterates of a natural number eventually reach a value at most one, using a bound
that decreases by at least one per iteration while all preceding iterates exceed one.

The mathematical setting follows [BuhrmanEtAl2005].

## Main statements

* `exists_iterLog_le_one`: existence of a stopping index.
* `logStar_spec` and `logStar_min`: the stopping property and minimality of `logStar`.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- The `k`-fold iteration of the real natural logarithm, with zero iterations returning the
input. -/
def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

/-- One additional logarithm iteration applies `Real.log` to the preceding iterate. -/
theorem iterLog_succ (k : ℕ) (x : ℝ) : iterLog (k + 1) x = Real.log (iterLog k x) :=
  rfl

/-- If every logarithm iterate through index `k` exceeds one, the `k`th iterate of `N` is at
most `N - k`. See [Buhrman et al., 2005, Theorem 7][BuhrmanEtAl2005]. -/
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

/-- For every natural number `N`, some iterated natural logarithm of `N` is at most one. See
[Buhrman et al., 2005, Theorem 7][BuhrmanEtAl2005]. -/
theorem exists_iterLog_le_one (N : ℕ) : ∃ k, iterLog k (N : ℝ) ≤ 1 := by
  by_contra h
  push Not at h
  have hle := iterLog_le_sub N N (fun j _ => h j)
  have hpos : 0 < iterLog N (N : ℝ) := lt_trans zero_lt_one (h N)
  have hnonpos : iterLog N (N : ℝ) ≤ 0 := by
    simpa using hle
  linarith

/-- The least number of natural logarithm iterations needed to send `N` to a value at most one. -/
noncomputable def logStar (N : ℕ) : ℕ :=
  Nat.find (exists_iterLog_le_one N)

/-- The iterate at index `logStar N` is at most one. See [Buhrman et al., 2005, Theorem
7][BuhrmanEtAl2005]. -/
theorem logStar_spec (N : ℕ) : iterLog (logStar N) (N : ℝ) ≤ 1 :=
  Nat.find_spec (exists_iterLog_le_one N)

/-- Any index at which the iterated logarithm is at most one is at least `logStar N`. -/
theorem logStar_min {N k : ℕ} (h : iterLog k (N : ℝ) ≤ 1) : logStar N ≤ k :=
  Nat.find_min' (exists_iterLog_le_one N) h

end Qatlib.Papers.ElemDistinct00.MainResults.BothOrderedClaw
