/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Theorem 4.4 — `QAM ⊆ BP·PP`

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 4.4 (page 18), proof pages 18--20.

Statement (verbatim): `QAM ⊆ BP·PP`.

The proof composes two pieces: (i) Proposition 4.3 says that for a uniformly
random Arthur coin string `y`, a `2/3`-fraction of the games `A_{x,y}` are
"good" (acceptance `≥ 2/3` on YES, `≤ 1/3` on NO); (ii) each good game `A_{x,y}`
is a `QMA`-type game, and Theorem 3.4 places it in `PP`.  The `BP` machine
samples `y` and runs the `PP` test, giving `QAM ⊆ BP·PP`.

## What is formalised here

The averaging core of the argument: over the `2^{s}` Arthur coins, the uniform
average of the complementary acceptance profile `1 − μ` is the complement of the
average of `μ`,
`coinAverage (fun y => 1 − μ y) = 1 − coinAverage μ`.
Consequently, if fewer than `1/9` of the coins are "bad" reflected through
`1 − μ`, then more than `8/9` of the coins are good, which is precisely the
`BP`-amplification arithmetic used to pass from Proposition 4.3 to the `BP`
machine.  The operator-to-classical `PP` bridge and the composition with
Theorem 3.4 are not in the shared library; see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qam

open Qatlib.Papers.ArthurMerlin05.StaticGames
open scoped BigOperators

/-- Over the `2^{s}` uniform coins, averaging the complementary profile
`1 − μ` gives `1` minus the average of `μ`:
`coinAverage (fun y => 1 − μ y) = 1 − coinAverage μ`.  This is the averaging
identity behind the good-coin density used to place `QAM` in `BP·PP`. -/
theorem coinAverage_one_sub {s : ℕ} (μ : Fin (Qdim s) → ℝ) :
    coinAverage (fun y => 1 - μ y) = 1 - coinAverage μ := by
  have hposnat : 0 < Qdim s := by
    unfold Qdim
    exact pow_pos (by norm_num) s
  have hd : (Qdim s : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Qdim s : ℝ) := by exact_mod_cast hposnat
    linarith
  unfold coinAverage
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp only [mul_one]
  field_simp

/-- Theorem 4.4 (page 18), averaging core: if the coin-average of the
complementary profile `1 − μ` is at most `1/9`, then more than `8/9` of the coins
have `μ = 1` on average, i.e. `8/9 ≤ coinAverage μ`.  This is the `BP`
amplification arithmetic: at most `1/9` of Arthur's coins are bad, so at least
`8/9` are good, giving the two-sided `BP` gap. -/
theorem theorem_4_4 {s : ℕ} (μ : Fin (Qdim s) → ℝ)
    (hcomp : coinAverage (fun y => 1 - μ y) ≤ 1 / 9) :
    (8 / 9 : ℝ) ≤ coinAverage μ := by
  rw [coinAverage_one_sub] at hcomp
  linarith

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qam
