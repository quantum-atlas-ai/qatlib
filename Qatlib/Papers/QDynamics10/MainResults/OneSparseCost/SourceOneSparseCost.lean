/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.OneSparseCost — c009 (Lemma 9)

Fixed source: arXiv:1011.3489v1, Lemma 9 (p. 15), Eq. (65); proof on p. 15–16.

Lemma 9. Let `n = ⌈log₂(d²ῩΔt/ε)⌉` (the number of exponential-precision bits) and `n_H` be
the number of bits of precision used to represent the matrix elements of the `H_μ`. Using the
BACS approach of Ref. [8] to simulate each exponential, the number of quantum operations `C`
needed to simulate each exponential satisfies

  `C ≤ 4 n (z_n + 2) + 3 n_H`,                                                         (65)

where `z_n` is obtained by iterating the map `z ↦ ⌈2 log₂ z⌉` until `z ≤ 6` (at most `O(log* n)`
iterations).

Proof route (p. 15–16): BACS uses `4n` rotations per round and `z` rounds; the round count `z`
is itself simulated by a recursive BACS construction needing `4n(z_n + 2)` operations in
total, and each QMatrixVal query costs `3` rotations, giving `3 n_H`; total `4n(z_n+2)+3n_H`.

Formalisation.

* `zStep` is the map `z ↦ ⌈2 log₂ z⌉` of the paper; `zIter` its `k`-fold iterate; `zCount n`
  the first `k` with `zIter k n ≤ 6` (Mathlib has no `log*`; the count is via `Nat.find`).
* `zIter_exists` uses only the paper's two structural facts about the map,
  `zStep m ≤ m` (`hzle`) and `6 < m → zStep m < m` (`hzlt`), which we take as hypotheses
  (they hold for `⌈2log₂z⌉` for `z ≥ 7`; proving them for the `Real.logb`/`Nat.ceil`
  formulation is routine real analysis not needed for the counting argument).
* `lemma9` then proves Eq. (65) by strong induction on `n`, using the recurrence
  `C n ≤ 4n + C(zStep n)` for `n > 6` and the base `C n ≤ 3 n_H` for `n ≤ 6`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.OneSparseCost

open Qatlib.Papers.QDynamics10.MainResults

/-- The map `z ↦ ⌈2 log₂ z⌉` iterated in the proof of Lemma 9 (p. 15): one "round" of the
recursive BACS construction halves the exponent bits needed. -/
def zStep (z : ℕ) : ℕ := Nat.ceil (2 * Real.logb 2 (z : ℝ))

/-- `k`-fold iteration of `zStep`. -/
def zIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => zIter k (zStep n)

/-- Iterating the strictly decreasing map `zStep` (away from `≤ 6`) reaches `≤ 6`. -/
theorem zIter_exists (hzlt : ∀ m, 6 < m → zStep m < m) : ∀ n : ℕ, ∃ k, zIter k n ≤ 6 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with hn | hn
    · exact ⟨0, by simp [zIter]; omega⟩
    · have hn6 : 6 < n := by omega
      obtain ⟨k, hk⟩ := ih (zStep n) (hzlt n hn6)
      exact ⟨k + 1, by simpa [zIter] using hk⟩

/-- The number `z_n` of Lemma 9: the first iterate of `zStep` that is at most `6`. -/
def zCount (n : ℕ) (hzlt : ∀ m, 6 < m → zStep m < m) : ℕ :=
  Nat.find (zIter_exists hzlt n)

/-- `zCount` reaches `≤ 6`: the defining property of `z_n`. -/
theorem zCount_spec (n : ℕ) (hzlt : ∀ m, 6 < m → zStep m < m) :
    zIter (zCount n hzlt) n ≤ 6 := by
  simpa [zCount] using Nat.find_spec (zIter_exists hzlt n)

/-- Minimality of `zCount`. -/
theorem zCount_min (n : ℕ) (hzlt : ∀ m, 6 < m → zStep m < m) {k : ℕ}
    (h : zIter k n ≤ 6) : zCount n hzlt ≤ k := by
  simpa [zCount] using Nat.find_min' (zIter_exists hzlt n) h

/-- For `n > 6` the count is positive: at least one iterative step is needed. -/
theorem zCount_pos (n : ℕ) (hzlt : ∀ m, 6 < m → zStep m < m) (hn : 6 < n) :
    0 < zCount n hzlt := by
  rcases Nat.eq_zero_or_pos (zCount n hzlt) with h | h
  · have := zCount_spec n hzlt
    rw [h] at this
    simp [zIter] at this
    omega
  · exact h

/-- One-step decrease of the count: after one `zStep` the iteration count drops by at least
one (`z_{zStep n} ≤ z_n − 1` for `n > 6`). -/
theorem zCount_step_le (n : ℕ) (hzlt : ∀ m, 6 < m → zStep m < m) (hn : 6 < n) :
    zCount (zStep n) hzlt ≤ zCount n hzlt - 1 := by
  have hpos := zCount_pos n hzlt hn
  obtain ⟨k, hk⟩ : ∃ k, zCount n hzlt = k + 1 := ⟨zCount n hzlt - 1, by omega⟩
  have hspec := zCount_spec n hzlt
  rw [hk] at hspec
  simp only [zIter] at hspec
  have := zCount_min (zStep n) hzlt hspec
  omega

/-- c009 — Lemma 9 (p. 15; Eq. (65)).

If `C n` counts the quantum operations to simulate one exponential with `n` bits of
exponential precision (BACS: `C n ≤ 4n + C(zStep n)` for `n > 6`, and `C n ≤ 3 n_H` for
`n ≤ 6`, as `4·6` rotations are absorbed in the constant), then

  `C n ≤ 4 n (z_n + 2) + 3 n_H`,

the bound of Eq. (65), where `z_n = zCount n` is the number of `zStep` iterations needed to
reach `≤ 6`.

`hzle` and `hzlt` are the paper's structural facts about `z ↦ ⌈2log₂z⌉` (monotone-decreasing
onto `≤ 6`), used only to make `zCount` well defined and to run the induction. -/
theorem lemma9 (n nH : ℕ) (C : ℕ → ℕ)
    (hzle : ∀ m, zStep m ≤ m) (hzlt : ∀ m, 6 < m → zStep m < m)
    (hSmall : ∀ m, m ≤ 6 → C m ≤ 3 * nH)
    (hRec : ∀ m, 6 < m → C m ≤ 4 * m + C (zStep m)) :
    C n ≤ 4 * n * (zCount n hzlt + 2) + 3 * nH := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with hn | hn
    · have h1 := hSmall n (by omega)
      have h2 : 3 * nH ≤ 4 * n * (zCount n hzlt + 2) + 3 * nH :=
        Nat.le_add_left _ _
      exact le_trans h1 h2
    · have hn6 : 6 < n := by omega
      have hrec := hRec n hn6
      have hzs : zStep n < n := hzlt n hn6
      have hih := ih (zStep n) hzs
      have hstep : zCount (zStep n) hzlt + 2 ≤ zCount n hzlt + 1 := by
        have hpos := zCount_pos n hzlt hn6
        have := zCount_step_le n hzlt hn6
        omega
      have hmono : 4 * (zStep n) * (zCount (zStep n) hzlt + 2)
          ≤ 4 * n * (zCount n hzlt + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 (hzle n)) hstep
      calc C n ≤ 4 * n + C (zStep n) := hrec
        _ ≤ 4 * n + (4 * (zStep n) * (zCount (zStep n) hzlt + 2) + 3 * nH) :=
            Nat.add_le_add_left hih (4 * n)
        _ ≤ 4 * n + (4 * n * (zCount n hzlt + 1) + 3 * nH) :=
            Nat.add_le_add_left (Nat.add_le_add_right hmono (3 * nH)) (4 * n)
        _ = 4 * n * (zCount n hzlt + 2) + 3 * nH := by ring

end Qatlib.Papers.QDynamics10.MainResults.OneSparseCost
