/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel
import Qatlib.Papers.ZeroSumGames19.MainResults.MatrixWeights.SourceLemma1
import Mathlib.MeasureTheory.Measure.Real

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — Lemma 4 (classical sparse implementation of Algorithm 1)

Fixed source: arXiv:1904.03180v1, Lemma 4, p.6.

Paper statement: let `s` be the maximum number of non-zero entries in a row and
`d` the maximum number of non-zero entries in a column of `A`. Algorithm 1 finds
an `ε`-optimal pair on a classical randomised computer with probability at least
`1−δ` in `(16/ε²) ln(nm/δ)` iterations, using `O(s ln m + d ln n)` time per
iteration and `s + d` queries to a sparse oracle for `A` (the oracle also returns
the locations of non-zero entries).

Boundary: cost contract only. The tree data structure of Figure 1 (page 6) and
the walk-down sampling are not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.ClassicalBackend

open MeasureTheory
open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel
open Qatlib.Papers.ZeroSumGames19.MainResults.MatrixWeights

/-- Lemma 4, p.6 (content decomposition).  As for Lemma 3: the accuracy
    certificate is Lemma 1's (`T = ⌈16 ln(nm/δ)/ε²⌉` rounds, probability
    `1−δ`); the sparse per-round cost `O(s ln m + d ln n)` time and `s+d`
    sparse-oracle queries is the data-structure half, recorded here as the
    total-cost arithmetic against the contract. -/
theorem source_lemma4_content
    {n m s d : ℕ} (hn : 0 < n) (hm : 0 < m) (hs : 0 < s) (hd : 0 < d)
    (A : PayoffMatrix n m)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ → Fin n → ℝ) (Y : Ω → ℕ → Fin m → ℝ)
    (hweights : ∀ ω t, 1 ≤ t →
      (∑ i, X ω t i) = (t : ℝ) * (ε / 4) ∧
      (∑ j, Y ω t j) = (t : ℝ) * (ε / 4))
    (hmarkov : 1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      potential A (X ω t) (Y ω t) ≤
        ((n : ℝ) * m / δ) * Real.exp (3 * (t : ℝ) * (ε / 4) ^ 2)}) :
    1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      EpsOptimal A (fun i => X ω t i / (∑ i, X ω t i))
        (fun j => Y ω t j / (∑ j, Y ω t j)) ε}
    ∧ ∀ C : ℝ, 0 < C →
        (fixedAccuracyRounds n m ε δ : ℝ)
            * (C * ((s : ℝ) * Real.log m + (d : ℝ) * Real.log n))
          = C * ((fixedAccuracyRounds n m ε δ : ℝ)
            * ((s : ℝ) * Real.log m + (d : ℝ) * Real.log n)) := by
  refine ⟨?_, fun C _ => by ring⟩
  exact source_lemma1_fixed_accuracy hn hm A hε0 hε1 hδ0 hδ1 X Y hweights hmarkov

end Qatlib.Papers.ZeroSumGames19.MainResults.ClassicalBackend
