/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The recurrences of Claim 4.4

Source: A. Cornelissen, A. S. Gilani, S. Patro, *Quantum algorithms for path and cycle
containment problems*, arXiv:2605.09017v2 (fixed version read for this file).

Claim 4.4 in §4 defines the two sequences `x_k`, `y_k` by

`x_{k+2} = (1 + x_k) / (2 - y_k)`, `y_{k+2} = (1 - y_k) / (2 (2 - y_k))`,
with `x_2 = 1/2`, `x_3 = 2/3`, `y_2 = y_3 = 1/2`,

because the recursion for the layered path algorithm of Lemma 4.2/4.3 produces a query
bound `Θ(n^{x_k + y_k α_r})`.  The claim asserts four things: the recurrences are
well-defined, `x_k + y_k` is increasing, `3/2 - (x_k + y_k) ∈ Θ(c^{-k})` with
`c = √(3 + √17) / 2`, and a formula for `α_{k+2,r}`.

This file formalizes the first two assertions (plus the explicit one-step identities that
drive them):

* `ySeq_bounds`, `xSeq_bounds` : the sequences stay in the range `0 < y_k ≤ 1/2` and
  `0 < x_k ≤ 2`, which is exactly the well-definedness argument of the paper;
* `sSeq_le` : `x_k + y_k ≤ 3/2` for all `k ≥ 2`;
* `sStep_identity` : `3/2 - (x_{k+2} + y_{k+2}) = (3/2 - (x_k + y_k)) / (2 - y_k)`,
  the recursion for the distance to the limit;
* `sSeq_mono` : `x_k + y_k ≤ x_{k+2} + y_{k+2}`;
* `xySeq_table` : the first values match the table printed in the proof of the claim.

The asymptotic statement `3/2 - (x_k + y_k) ∈ Θ(c^{-k})` and the `α_{k+2,r}` formula are
not formalized; see the PR discussion for the remaining gap.
-/

set_option autoImplicit false

namespace Qatlib.Papers.PathCycle26.MainResults

/-- The sequence `y_k` of Claim 4.4: `y_2 = y_3 = 1/2` and
`y_{k+2} = (1 - y_k) / (2 (2 - y_k))` for `k ≥ 2`.  Indices `0` and `1` are unused
filler, the recurrences only ever refer to indices `≥ 2`. -/
noncomputable def ySeq : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 1 / 2
  | 3 => 1 / 2
  | k + 4 => (1 - ySeq (k + 2)) / (2 * (2 - ySeq (k + 2)))

/-- The sequence `x_k` of Claim 4.4: `x_2 = 1/2`, `x_3 = 2/3` and
`x_{k+2} = (1 + x_k) / (2 - y_k)` for `k ≥ 2`.  Indices `0` and `1` are unused filler,
the recurrences only ever refer to indices `≥ 2`. -/
noncomputable def xSeq : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 2 / 3
  | 2 => 1 / 2
  | 3 => 2 / 3
  | k + 4 => (1 + xSeq (k + 2)) / (2 - ySeq (k + 2))

/-- The one-step recursion for `y`, stated at the paper's indices: for `k ≥ 4` the value
`y_k` is the image of `y_{k-2}`. -/
theorem ySeq_step {k : ℕ} (hk : 4 ≤ k) :
    ySeq k = (1 - ySeq (k - 2)) / (2 * (2 - ySeq (k - 2))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  have h : j + 4 - 2 = j + 2 := by omega
  simp only [ySeq, h]

/-- The one-step recursion for `x`, stated at the paper's indices: for `k ≥ 4` the value
`x_k` is the image of `x_{k-2}` under the map with parameter `y_{k-2}`. -/
theorem xSeq_step {k : ℕ} (hk : 4 ≤ k) :
    xSeq k = (1 + xSeq (k - 2)) / (2 - ySeq (k - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  have h : j + 4 - 2 = j + 2 := by omega
  simp only [xSeq, h]

/-- The one-step estimate behind the well-definedness of the recurrences: the map
`y ↦ (1 - y) / (2 (2 - y))` sends `(0, 1/2]` into itself. -/
theorem yStep_bounds {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 2) :
    0 < (1 - y) / (2 * (2 - y)) ∧ (1 - y) / (2 * (2 - y)) ≤ 1 / 2 := by
  have hden : 0 < 2 * (2 - y) := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_le_iff₀ hden]
    linarith

/-- The one-step estimate behind `x_k ≤ 2`: if `0 ≤ x ≤ 2` and `0 < y ≤ 1/2`, then
`0 < (1 + x) / (2 - y) ≤ 2`. -/
theorem xStep_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hy0 : 0 < y)
    (hy1 : y ≤ 1 / 2) :
    0 < (1 + x) / (2 - y) ∧ (1 + x) / (2 - y) ≤ 2 := by
  have hden : 0 < 2 - y := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_le_iff₀ hden]
    linarith

/-- The recurrences are well-defined: for all `k ≥ 2` we have `0 < y_k ≤ 1/2`, so the
denominators `2 - y_k` and `2 (2 - y_k)` never vanish. -/
theorem ySeq_bounds : ∀ k : ℕ, 2 ≤ k → 0 < ySeq k ∧ ySeq k ≤ 1 / 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      by_cases h4 : k < 4
      · interval_cases k <;> norm_num [ySeq]
      · have hk4 : 4 ≤ k := by omega
        rw [ySeq_step hk4]
        exact yStep_bounds (ih (k - 2) (by omega) (by omega)).1
          (ih (k - 2) (by omega) (by omega)).2

/-- The recursion for `x` is well-defined and keeps `0 < x_k ≤ 2`. -/
theorem xSeq_bounds : ∀ k : ℕ, 2 ≤ k → 0 < xSeq k ∧ xSeq k ≤ 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      by_cases h4 : k < 4
      · interval_cases k <;> norm_num [xSeq]
      · have hk4 : 4 ≤ k := by omega
        rw [xSeq_step hk4]
        exact xStep_bounds (ih (k - 2) (by omega) (by omega)).1.le
          (ih (k - 2) (by omega) (by omega)).2
          (ySeq_bounds (k - 2) (by omega)).1 (ySeq_bounds (k - 2) (by omega)).2

/-- One step of the sum `x_k + y_k`, in closed form. -/
theorem sStep_eq {x y : ℝ} (hy : y ≠ 2) :
    (1 + x) / (2 - y) + (1 - y) / (2 * (2 - y)) = (3 + 2 * x - y) / (2 * (2 - y)) := by
  have hden : 2 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have h2 : 2 * (2 - y) ≠ 0 := mul_ne_zero two_ne_zero hden
  field_simp
  ring

/-- The distance to the limit shrinks by the factor `1 / (2 - y_k)` per step.  This is
the identity behind the asymptotic rate `3/2 - (x_k + y_k) ∈ Θ(c^{-k})`. -/
theorem sStep_identity {x y : ℝ} (hy : y ≠ 2) :
    3 / 2 - ((1 + x) / (2 - y) + (1 - y) / (2 * (2 - y))) =
      (3 / 2 - (x + y)) / (2 - y) := by
  have hden : 2 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have h2 : 2 * (2 - y) ≠ 0 := mul_ne_zero two_ne_zero hden
  field_simp
  ring

/-- The sum `x_k + y_k` stays at most `3/2` for all `k ≥ 2`. -/
theorem sSeq_le : ∀ k : ℕ, 2 ≤ k → xSeq k + ySeq k ≤ 3 / 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      by_cases h4 : k < 4
      · interval_cases k <;> norm_num [xSeq, ySeq]
      · have hk4 : 4 ≤ k := by omega
        have hx0 := (xSeq_bounds (k - 2) (by omega)).1.le
        have hy0 := (ySeq_bounds (k - 2) (by omega)).1
        have hy1 := (ySeq_bounds (k - 2) (by omega)).2
        rw [xSeq_step hk4, ySeq_step hk4, sStep_eq (by linarith)]
        have hden : 0 < 2 * (2 - ySeq (k - 2)) := by linarith
        rw [div_le_iff₀ hden]
        nlinarith [ih (k - 2) (by omega) (by omega)]

/-- The recursion reproduces the table printed in the proof of Claim 4.4
(`y_4 = y_5 = 1/6`, `y_6 = 5/22`, `x_4 = 1`, `x_5 = 10/9`, `x_6 = 12/11`), which pins the
transcription of the recurrences. -/
theorem xySeq_table :
    ySeq 4 = 1 / 6 ∧ ySeq 5 = 1 / 6 ∧ ySeq 6 = 5 / 22 ∧
      xSeq 4 = 1 ∧ xSeq 5 = 10 / 9 ∧ xSeq 6 = 12 / 11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [ySeq, xSeq]

/-- The distance `3/2 - (x_k + y_k)` to the limit is strictly positive for all `k ≥ 2`.
This upgrades the paper's "well-definedness" induction to the strict inequality that
drives the rate statement: the sum never reaches its upper bound `3/2`. -/
theorem dSeq_pos : ∀ k : ℕ, 2 ≤ k → 0 < 3 / 2 - (xSeq k + ySeq k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      by_cases h4 : k < 4
      · interval_cases k <;> norm_num [xSeq, ySeq]
      · have hk4 : 4 ≤ k := by omega
        have hy1 := (ySeq_bounds (k - 2) (by omega)).2
        have hden : 0 < 2 - ySeq (k - 2) := by linarith
        rw [xSeq_step hk4, ySeq_step hk4, sStep_identity (by linarith)]
        exact div_pos (ih (k - 2) (by omega) (by omega)) hden

/-- The sum `x_k + y_k` is *strictly* increasing along the recursion, in steps of two.
Equivalently, the distance `3/2 - (x_k + y_k)` is strictly decreasing, because each
step divides it by the factor `1 / (2 - y_k) < 1`. -/
theorem sSeq_lt_mono : ∀ k : ℕ, 2 ≤ k →
    xSeq k + ySeq k < xSeq (k + 2) + ySeq (k + 2) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hstepx : xSeq (j + 2 + 2) = (1 + xSeq (j + 2)) / (2 - ySeq (j + 2)) := by
    simp only [xSeq]
  have hstepy : ySeq (j + 2 + 2) = (1 - ySeq (j + 2)) / (2 * (2 - ySeq (j + 2))) := by
    simp only [ySeq]
  have hy1 := (ySeq_bounds (j + 2) (by omega)).2
  have hpos := dSeq_pos (j + 2) (by omega)
  have hden : 0 < 2 - ySeq (j + 2) := by linarith
  have hid := sStep_identity (x := xSeq (j + 2)) (y := ySeq (j + 2)) (by linarith)
  have hlt : (3 / 2 - (xSeq (j + 2) + ySeq (j + 2))) / (2 - ySeq (j + 2)) <
      3 / 2 - (xSeq (j + 2) + ySeq (j + 2)) := by
    rw [div_lt_iff₀ hden]
    nlinarith [hpos, hy1]
  rw [hstepx, hstepy]
  linarith [hid ▸ hlt]

/-- The two-step recursion for `x`, stated at index `k + 2` for every `k ≥ 2`. -/
theorem xSeq_succ2 {k : ℕ} (hk : 2 ≤ k) :
    xSeq (k + 2) = (1 + xSeq k) / (2 - ySeq k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [xSeq]

/-- The two-step recursion for `y`, stated at index `k + 2` for every `k ≥ 2`. -/
theorem ySeq_succ2 {k : ℕ} (hk : 2 ≤ k) :
    ySeq (k + 2) = (1 - ySeq k) / (2 * (2 - ySeq k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [ySeq]

/-- The distance to the limit shrinks by at most a factor `2/3` every two steps:
`3/2 - (x_{k+2} + y_{k+2}) ≤ (2/3) · (3/2 - (x_k + y_k))`.  This uses that
`2 - y_k ≥ 3/2`. -/
theorem dStep_le (k : ℕ) (hk : 2 ≤ k) :
    3 / 2 - (xSeq (k + 2) + ySeq (k + 2)) ≤
      (2 / 3) * (3 / 2 - (xSeq k + ySeq k)) := by
  have hy1 := (ySeq_bounds k hk).2
  have hden : 0 < 2 - ySeq k := by linarith
  have hd : 0 ≤ 3 / 2 - (xSeq k + ySeq k) := (dSeq_pos k hk).le
  have hid := sStep_identity (x := xSeq k) (y := ySeq k) (by linarith)
  rw [xSeq_succ2 hk, ySeq_succ2 hk, hid]
  rw [div_le_iff₀ hden]
  nlinarith [hy1, hd]

/-- The distance to the limit shrinks by at least a factor `1/2` every two steps:
`(1/2) · (3/2 - (x_k + y_k)) ≤ 3/2 - (x_{k+2} + y_{k+2})`.  This uses that
`2 - y_k ≤ 2`. -/
theorem dStep_ge (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2) * (3 / 2 - (xSeq k + ySeq k)) ≤
      3 / 2 - (xSeq (k + 2) + ySeq (k + 2)) := by
  have hy0 := (ySeq_bounds k hk).1
  have hy1 := (ySeq_bounds k hk).2
  have hden : 0 < 2 - ySeq k := by linarith
  have hd : 0 ≤ 3 / 2 - (xSeq k + ySeq k) := (dSeq_pos k hk).le
  have hid := sStep_identity (x := xSeq k) (y := ySeq k) (by linarith)
  rw [xSeq_succ2 hk, ySeq_succ2 hk, hid]
  rw [le_div_iff₀ hden]
  nlinarith [hy0, hy1, hd]

/-- Iterated upper bound: after `m` two-step recursions the distance to the limit is at
most `(2/3)^m` times its starting value.  This is the explicit exponential decay behind
`3/2 - (x_k + y_k) ∈ Θ(c^{-k})`. -/
theorem dSeq_le_iter (k : ℕ) (hk : 2 ≤ k) :
    ∀ m : ℕ,
      3 / 2 - (xSeq (k + 2 * m) + ySeq (k + 2 * m)) ≤
        (2 / 3) ^ m * (3 / 2 - (xSeq k + ySeq k)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hk' : 2 ≤ k + 2 * m := by omega
      have hstep := dStep_le (k + 2 * m) hk'
      have : k + 2 * (m + 1) = k + 2 * m + 2 := by omega
      rw [this]
      have hfac : (0 : ℝ) ≤ (2 / 3) ^ m := by positivity
      have hd : 0 ≤ 3 / 2 - (xSeq k + ySeq k) := (dSeq_pos k hk).le
      calc
        3 / 2 - (xSeq (k + 2 * m + 2) + ySeq (k + 2 * m + 2))
            ≤ (2 / 3) * (3 / 2 - (xSeq (k + 2 * m) + ySeq (k + 2 * m))) := hstep
        _ ≤ (2 / 3) * ((2 / 3) ^ m * (3 / 2 - (xSeq k + ySeq k))) := by
              nlinarith [ih, hfac]
        _ = (2 / 3) ^ (m + 1) * (3 / 2 - (xSeq k + ySeq k)) := by ring

/-- Iterated lower bound: after `m` two-step recursions the distance to the limit is at
least `(1/2)^m` times its starting value. -/
theorem dSeq_ge_iter (k : ℕ) (hk : 2 ≤ k) :
    ∀ m : ℕ,
      (1 / 2) ^ m * (3 / 2 - (xSeq k + ySeq k)) ≤
        3 / 2 - (xSeq (k + 2 * m) + ySeq (k + 2 * m)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hk' : 2 ≤ k + 2 * m := by omega
      have hstep := dStep_ge (k + 2 * m) hk'
      have : k + 2 * (m + 1) = k + 2 * m + 2 := by omega
      rw [this]
      have hfac : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
      have hd : 0 ≤ 3 / 2 - (xSeq k + ySeq k) := (dSeq_pos k hk).le
      calc
        (1 / 2) ^ (m + 1) * (3 / 2 - (xSeq k + ySeq k))
            = (1 / 2) * ((1 / 2) ^ m * (3 / 2 - (xSeq k + ySeq k))) := by ring
        _ ≤ (1 / 2) * (3 / 2 - (xSeq (k + 2 * m) + ySeq (k + 2 * m))) := by
              nlinarith [ih, hfac]
        _ ≤ 3 / 2 - (xSeq (k + 2 * m + 2) + ySeq (k + 2 * m + 2)) := hstep

/-- The sum `x_k + y_k` is nondecreasing along the recursion, in steps of two. -/
theorem sSeq_mono : ∀ k : ℕ, 2 ≤ k → xSeq k + ySeq k ≤ xSeq (k + 2) + ySeq (k + 2) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hstepx : xSeq (j + 2 + 2) = (1 + xSeq (j + 2)) / (2 - ySeq (j + 2)) := by
    simp only [xSeq]
  have hstepy : ySeq (j + 2 + 2) = (1 - ySeq (j + 2)) / (2 * (2 - ySeq (j + 2))) := by
    simp only [ySeq]
  have hy1 := (ySeq_bounds (j + 2) (by omega)).2
  have hs := sSeq_le (j + 2) (by omega)
  rw [hstepx, hstepy]
  have hid := sStep_identity (x := xSeq (j + 2)) (y := ySeq (j + 2)) (by linarith)
  have hz : 0 ≤ 3 / 2 - (xSeq (j + 2) + ySeq (j + 2)) := by linarith
  have hden : 0 < 2 - ySeq (j + 2) := by linarith
  have hle :
      (3 / 2 - (xSeq (j + 2) + ySeq (j + 2))) / (2 - ySeq (j + 2)) ≤
        3 / 2 - (xSeq (j + 2) + ySeq (j + 2)) := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

end Qatlib.Papers.PathCycle26.MainResults
