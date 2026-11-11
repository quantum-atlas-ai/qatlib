/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 8 — the success probability of Algorithm 4

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Lemma 8 is printed on p.11 (§4.2,
eq. (12)) and proved on p.16 (§4.4).

The source decomposes the input along the eigenbasis,
`|x⟩ = ∑_i α_i |v_i⟩`, and observes that each invariant subspace
`|v_i⟩ ⊗ H_A ⊗ H_S ⊗ H_E` evolves separately, so the success probability of
Algorithm 4 is the weighted sum of the per-branch success probabilities:

  `psucc = ∑_i |α_i|² · q_i`,

where `q_i` is the probability that the branch starting in `|v_i⟩` stops with
output register `|1⟩`.  In the branch proof the source derives
`q_i = Ω(ε² 2^{2 j_i}/κ²)` (Claim 1 gives `λ_i = O(ε 2^{j_i})` and the
amplitude of `|1⟩` in step (3b) is `1/(κλ_i)`), so

  `psucc = Ω(∑_i |α_i|² ε² 2^{2 j_i}/κ²)`   (eq. (12)).

The Lean statement below is that finite weighted-sum step with the branch
constant made explicit: each branch success probability dominates
`(1/4)·ε²·2^{2 j_i}/κ²` (the constant in the source's `Ω`), and the global
success probability is the `|α_i|²`-weighted sum.  The statement is faithful
to eq. (12) up to the explicit absolute constant `1/4` that the source leaves
inside `Ω`; no success floor or uniformity assumption is added beyond the
per-branch lower bound that the source's Claim 1 supplies.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

/-- Fixed arXiv:1010.4458v2, Lemma 8 (printed p.11, eq. (12); proved p.16).

For a finite eigenbasis `ι`, branch weights `α : ι → ℝ` (the `|α_i|` of the
input decomposition), branch success probabilities `q : ι → ℝ`, and stage
indices `j : ι → ℕ`, if every branch satisfies the source's per-branch lower
bound `q_i ≥ (1/4)·ε²·2^{2j_i}/κ²`, then the global success probability
`psucc = ∑_i |α_i|² q_i` satisfies

  `psucc ≥ (1/4)·∑_i |α_i|²·ε²·2^{2j_i}/κ²`,

which is the source's `Ω(∑_i |α_i|² ε² 2^{2j_i}/κ²)` with the absolute
constant `1/4` made explicit. -/
theorem source_lemma8 {ι : Type} [Fintype ι]
    (α q : ι → ℝ) (j : ι → ℕ) (ε κ : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ)
    (hq : ∀ i, (1 / 4) * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2 ≤ q i) :
    (1 / 4) * (∑ i, α i ^ 2 * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2)
      ≤ ∑ i, α i ^ 2 * q i := by
  classical
  have hterm : ∀ i, α i ^ 2 * ((1 / 4) * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2)
      ≤ α i ^ 2 * q i := by
    intro i
    exact mul_le_mul_of_nonneg_left (hq i) (sq_nonneg _)
  have hsplit : (1 / 4) * (∑ i, α i ^ 2 * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2)
      = ∑ i, α i ^ 2 * ((1 / 4) * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  exact Finset.sum_le_sum fun i _ => hterm i

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
