/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.1 of TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Lemma 4.1, printed p. 8.

"Let `k` be any constant such that `0 ≤ k ≤ 1`.  Suppose that `X` is a set
obtained by taking uniformly at random, with replacement, `⌈3 n^k log n⌉`
elements from `V`.  Then `X` is `k`-good for `G` with probability at least
`1 - 1/n`."

The sample space is formalised as all functions `Fin m → V` (the `m` draws,
with replacement), equipped with the uniform law; `X` is the image of the
function.  `KGood` is Definition 4.1 of the paper.

This layer is a conditional theorem.  The hypothesis `hTail` isolates the
unformalized probabilistic core: the sum, over all subsets `Y ⊆ V`, of the
probabilities that the drawn sample violates the `k`-goodness inequality at
`Y`, is at most `1/n`.  What is proved here is the paper's finite union bound
layer: the failure event `¬ KGood` is the union over `Y ⊆ V` of the per-`Y`
violation events, its cardinality is bounded by `Finset.card_biUnion_le`, and
complementing within the finite sample space turns the failure bound into the
`1 - 1/n` success bound.  The side condition `2 ≤ |V|` makes the sample space
nonempty (the paper works with `n` large throughout Section 4).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

variable {V : Type*}

/-- The number of draws `m = ⌈3 n^k log n⌉` of Lemma 4.1. -/
def sampleCount (n : ℕ) (k : ℝ) : ℕ :=
  Nat.ceil (3 * Real.rpow (n : ℝ) k * Real.log (n : ℝ))

/-- The event that the sample image `X` violates the `k`-goodness inequality
of Definition 4.1 at the subset `Y`: the negated inequality inside `KGood`. -/
def violatesKGoodAt [Fintype V] (G : SimpleGraph V) (k : ℝ) (X Y : Finset V) : Prop :=
  ¬ (∑ w : V, ((deltaSetW G X Y w).card : ℝ)) ≤
      (Y.card : ℝ) ^ 2 * Real.rpow (Fintype.card V : ℝ) (1 - k)

/-- Lemma 4.1 of arXiv:1407.0085v2 (printed p. 8, proof pp. 8–9), conditional
union-bound form.  If the summed per-subset violation probabilities of the
`⌈3 n^k log n⌉`-draw sample are at most `1/n`, then the sample image is
`k`-good with probability at least `1 - 1/n`.

The unformalized gap is the per-subset tail estimate itself: the paper derives
it from `(1 - t/n)^m ≤ exp(-mt/n)` at `t > n^{1-k}`, the union bound over the
pairs of `V.powersetCard 2`, and the counting identity
`∑_w |Δ_G(X,Y,w)| = ∑_{e ∈ Δ_G(X,Y)} |{w | e ⊆ N_G(w)}|` (pp. 8–9).  Candidate
dependencies: `Real.one_sub_div_pow_le_exp_neg`, `Finset.card_le_card`,
`Finset.sum_le_sum`. -/
theorem source_lemma_4_1 (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℝ) (_hk0 : 0 ≤ k) (_hk1 : k ≤ 1)
    (hnV : 2 ≤ Fintype.card V)
    (hTail : ∑ Y ∈ (Finset.univ : Finset (Finset V)),
        uniformProb (fun s : Fin (sampleCount (Fintype.card V) k) → V =>
          violatesKGoodAt G k (Finset.image s Finset.univ) Y)
      ≤ 1 / (Fintype.card V : ℝ)) :
    (1 : ℝ) - 1 / (Fintype.card V : ℝ) ≤
      uniformProb (fun s : Fin (sampleCount (Fintype.card V) k) → V =>
        KGood G (Finset.image s Finset.univ) k) := by
  classical
  have hVNE : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hΩNE : Nonempty (Fin (sampleCount (Fintype.card V) k) → V) :=
    ⟨fun _ => Classical.arbitrary V⟩
  have hfail : uniformProb (fun s : Fin (sampleCount (Fintype.card V) k) → V =>
        ¬ KGood G (Finset.image s Finset.univ) k)
      ≤ ∑ Y ∈ (Finset.univ : Finset (Finset V)),
          uniformProb (fun s : Fin (sampleCount (Fintype.card V) k) → V =>
            violatesKGoodAt G k (Finset.image s Finset.univ) Y) := by
    refine uniformProb_union_bound (t := (Finset.univ : Finset (Finset V))) _ _ ?_
    intro s hs
    by_contra hc
    push Not at hc
    exact hs (fun Y => not_not.mp (hc Y (Finset.mem_univ Y)))
  have h1 : uniformProb (fun s : Fin (sampleCount (Fintype.card V) k) → V =>
      ¬ KGood G (Finset.image s Finset.univ) k) ≤ 1 / (Fintype.card V : ℝ) :=
    le_trans hfail hTail
  have h2 := uniformProb_compl
    (p := fun s : Fin (sampleCount (Fintype.card V) k) → V =>
      KGood G (Finset.image s Finset.univ) k)
  linarith

end Qatlib.Papers.TriangleFind14.MainResults
