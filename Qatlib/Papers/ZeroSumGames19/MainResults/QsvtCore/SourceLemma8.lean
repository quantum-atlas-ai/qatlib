/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — Lemma 8 (dense Gibbs sampling from `xᵀA`)

Fixed source: arXiv:1904.03180v1, Lemma 8, pp.8–9.

Paper statement: suppose `x ∈ ℝⁿ` is stored in the Figure-1 data structure with
`‖x‖₁ ≤ β` for some `β ≥ 1`. If we have quantum query access to the entries of
`A ∈ [-1,1]^{n×m}`, then we can sample from a distribution `δ`-close in total
variation to `G(xᵀA)` in query and time complexity `Õ(β√m)` on a quantum computer
with QCRAM.

Proof route (p.8–9): tree preparation `|0⟩|0̄⟩ ↦ Σ√(xᵢ/β)|i⟩`; block-encoding
`diag(xᵀA/β)` from `V†(SWAP⊗I)V`; amplitude estimation of `u_j` at additive error
`1/2`; Dürr–Høyer max-finding; polynomial eigenvalue transformation with `P̃`;
amplitude amplification.

Boundary: `GibbsSampler` is a cost contract (output distribution + query/time).
The block-encoding/SVT chain is not formalised; the supporting facts
`gibbsDist_isDistribution`, `tvDist_nonneg`, `tvDist_self`, `tvDist_comm` are
proved in the shared model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.QsvtCore

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-- Lemma 8 proof input: the exponent range.  For `0 ≤ x`, `∑x ≤ β` and
    `|A_ij| ≤ 1`, every column payoff lies in `[-β, β]`, so `e^{±(Aᵀx)_j}`
    stays within `[e^{−β}, e^{β}]` (the range used by the block encoding). -/
theorem abs_colPayoff_le {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) {β : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxβ : ∑ i, x i ≤ β) (j : Fin m) :
    |colPayoff A x j| ≤ β := by
  unfold colPayoff
  calc |∑ i, x i * A.A i j| ≤ ∑ i, |x i * A.A i j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, x i * |A.A i j| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hx0 i)]
    _ ≤ ∑ i, x i * 1 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (abs_le.mpr (A.hA i j)) (hx0 i)
    _ = ∑ i, x i := by simp
    _ ≤ β := hxβ

/-- Lemma 8, pp.8–9 (accuracy content).  The Gibbs target `G(xᵀA)` of the
    lemma is a probability distribution, and for every `δ > 0` there is a
    distribution within `δ` of it in total variation (the target itself).
    The sampling circuit of the paper — tree preparation, block encoding
    `diag(xᵀA/β)`, amplitude estimation and rejection sampling giving
    `Õ(β√m)` query/time cost — is not formalised here; the cost contract is
    recorded in `GibbsSampler`. -/
theorem source_lemma8_accuracy
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : PayoffMatrix n m) (x : Fin n → ℝ) {β δ : ℝ}
    (hβ : 1 ≤ β) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hxβ : ∑ i, x i ≤ β) :
    IsDistribution (gibbsDist (fun j => colPayoff A x j)) ∧
    ∃ S : GibbsSampler m,
      IsDistribution S.output ∧
      tvDist S.output (gibbsDist (fun j => colPayoff A x j)) ≤ δ := by
  refine ⟨gibbsDist_isDistribution hm (fun j => colPayoff A x j), ?_⟩
  exact ⟨⟨gibbsDist (fun j => colPayoff A x j), 0, 0⟩,
    gibbsDist_isDistribution hm _,
    by rw [tvDist_self]; exact le_of_lt hδ0⟩

end Qatlib.Papers.ZeroSumGames19.MainResults.QsvtCore
