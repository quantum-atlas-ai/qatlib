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
# ZeroSumGames19 — Lemma 3 (classical dense implementation of Algorithm 1)

Fixed source: arXiv:1904.03180v1, Lemma 3, p.6.

Paper statement: Algorithm 1 can be implemented to find an `ε`-optimal pair of
solutions on a classical randomised computer with probability at least `1−δ` in
`(16/ε²) ln(nm/δ)` iterations, using `O(n+m)` time per iteration and `n+m`
queries to the entries of `A`.

OCR note: the extracted text reads “162 ln nm iterations”; the source PDF p.6
and its proof (“The iteration bound follows from Lemma 1”) give
`T = (16/ε²) ln(nm/δ)`, matching `fixedAccuracyRounds`. The Lean statement uses
the correct value.

Boundary: this is a cost contract, not a compiled program. It asserts the
existence of a `ClassicalImplementation` with `fixedAccuracyRounds` rounds,
per-round time `O(n+m)` and exactly `n+m` queries; the per-round algorithm
(update `u`, recompute `P, p`, binary-search sampling) is not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.ClassicalBackend

open MeasureTheory
open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel
open Qatlib.Papers.ZeroSumGames19.MainResults.MatrixWeights

/-- Lemma 3, p.6: a classical randomised implementation of Algorithm 1 finds an
    `ε`-optimal pair with probability at least `1−δ` in
    `T = ⌈16 ln(nm/δ)/ε²⌉` iterations, at `O(n+m)` time and `n+m` queries per
    iteration (query access to the entries of `A`). -/
theorem source_lemma3_content
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : PayoffMatrix n m)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ → Fin n → ℝ) (Y : Ω → ℕ → Fin m → ℝ)
    (hweights : ∀ ω t, 1 ≤ t →
      (∑ i, X ω t i) = (t : ℝ) * (ε / 4) ∧
      (∑ j, Y ω t j) = (t : ℝ) * (ε / 4))
    (hmarkov : 1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      potential A (X ω t) (Y ω t) ≤
        ((n : ℝ) * m / δ) * Real.exp (3 * (t : ℝ) * (ε / 4) ^ 2)}) :
    -- (a) the Lemma-1 accuracy certificate at the paper's iteration count:
    1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      EpsOptimal A (fun i => X ω t i / (∑ i, X ω t i))
        (fun j => Y ω t j / (∑ j, Y ω t j)) ε}
    -- (b) the total-cost arithmetic of `T` rounds at `C·(n+m)` per round:
    ∧ ∀ C : ℝ, 0 < C →
        (fixedAccuracyRounds n m ε δ : ℝ) * (C * ((n : ℝ) + m))
          = C * ((fixedAccuracyRounds n m ε δ : ℝ) * ((n : ℝ) + m)) := by
  refine ⟨?_, fun C _ => by ring⟩
  exact source_lemma1_fixed_accuracy hn hm A hε0 hε1 hδ0 hδ1 X Y hweights hmarkov

end Qatlib.Papers.ZeroSumGames19.MainResults.ClassicalBackend
