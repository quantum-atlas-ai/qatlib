/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — Lemma 10 (sparse Gibbs sampling from `xᵀA`)

Fixed source: arXiv:1904.03180v1, Lemma 10, pp.9–11.

Paper statement: suppose `x ∈ ℝⁿ_{≥0}` has at most `t` non-zero entries and is
stored in the Figure-1 data structure, with `‖x‖₁ ≤ β` for `β ≥ 1`. If we have
quantum query access to a sparse oracle of `A ∈ [-1,1]^{n×m}` with `s`-sparse rows
and columns, then we can sample from a distribution `δ`-close in total variation
to `G(xᵀA)` in query and time complexity `Õ(β^{3/2}√s)` on a quantum computer with
QCRAM.

Proof route (p.9–11): reduce to `βs ≤ m/4` (else Lemma 8); split coordinates by
`w_j = Σ_i x_i|A_ij|` into `w_j ≤ 1` (near-uniform) and `w_j ≥ 1/2` (sample
`i ∼ x/β`, then `j ∝ |A_ij|/s`); threshold polynomial `Q̃`; combine the two
subnormalised Gibbs states with `N = 16em + 64βs e^{ũ_max}`; amplitude
amplification.

Boundary: cost contract; the two-regime rejection-sampling construction is not
formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.PairedPrepare

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel


/-- Lemma 10, pp.9–11 (accuracy content).  As for Lemma 8: the Gibbs target
    `G(xᵀA)` is a distribution and a `δ`-close distribution exists for every
    `δ > 0`; the sparse sampling circuit giving `Õ(β^{3/2}√s)` query/time
    cost is not formalised (the sparse oracle and QCRAM model are outside
    the paper-layer cost contracts). -/
theorem source_lemma10_accuracy
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : PayoffMatrix n m) (x : Fin n → ℝ) (t s : ℕ)
    {β δ : ℝ} (hβ : 1 ≤ β) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hxβ : ∑ i, x i ≤ β)
    (hx_sparse : (Function.support x).ncard ≤ t) :
    IsDistribution (gibbsDist (fun j => colPayoff A x j)) ∧
    ∃ S : GibbsSampler m,
      IsDistribution S.output ∧
      tvDist S.output (gibbsDist (fun j => colPayoff A x j)) ≤ δ := by
  refine ⟨gibbsDist_isDistribution hm (fun j => colPayoff A x j), ?_⟩
  exact ⟨⟨gibbsDist (fun j => colPayoff A x j), 0, 0⟩,
    gibbsDist_isDistribution hm _,
    by rw [tvDist_self]; exact le_of_lt hδ0⟩

end Qatlib.Papers.ZeroSumGames19.MainResults.PairedPrepare
