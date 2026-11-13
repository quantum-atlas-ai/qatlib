/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4.1 of TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Proposition 4.1, printed p. 9, proved in Section 4.2, pp. 13–14.

"Let `a` and `k` be two constants such that `0 < a, k < 1`.  Let `X` be a known
subset of `V` of size at most `⌈3 n^k log n⌉` that is `k`-good for `G`.  There
exists a quantum algorithm with query complexity

`Õ(n^{1/2+k} + n^{1/2+2a/3} + n^{1/2+a-k/2})`

that, given as input a set `A ∈ S(V, ⌈n^a⌉)` and the set `Δ_G(X,A)`, checks with
probability at least `2/3` if `Δ_G(X,A)` contains an edge of a triangle of
`G`."

The output interface is a Boolean answer on each measurement outcome of a
finite family; `acceptProbability` sums the probability of the answer `true`.
The known set `Δ_G(X,A)` is a side condition of the source algorithm and is not
an extra query: in the model it is derived from `G`, `X`, `A` exactly as in the
paper (`deltaSet`).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

/-- The observable interface of a quantum checking algorithm on `n` vertices:
a finite outcome family, a probability law depending on the graph and on the
input set `A`, and a Boolean answer per outcome. -/
structure TriangleCheckQuantumAlgorithm (n : ℕ) where
  /-- Worst-case number of adjacency-oracle queries. -/
  queries : ℕ
  /-- Measurement records of the algorithm. -/
  outcomes : Type
  outcomesFintype : Fintype outcomes
  /-- Probability of each measurement record. -/
  prob : SimpleGraph (Fin n) → Finset (Fin n) → outcomes → ℝ
  prob_nonneg : ∀ (G : SimpleGraph (Fin n)) (Aset : Finset (Fin n)) (ω : outcomes),
    0 ≤ prob G Aset ω
  prob_sum : ∀ (G : SimpleGraph (Fin n)) (Aset : Finset (Fin n)),
    (@Finset.univ outcomes outcomesFintype).sum (fun ω => prob G Aset ω) = 1
  /-- The Boolean answer (`true` = "contains a triangle edge"). -/
  answer : SimpleGraph (Fin n) → Finset (Fin n) → outcomes → Bool

/-- Probability that the checking algorithm answers `true`. -/
def TriangleCheckQuantumAlgorithm.acceptProbability
    {n : ℕ} (A : TriangleCheckQuantumAlgorithm n)
    (G : SimpleGraph (Fin n)) (Aset : Finset (Fin n)) : ℝ :=
  letI := A.outcomesFintype
  ∑ ω : A.outcomes,
    A.prob G Aset ω * (if A.answer G Aset ω then (1 : ℝ) else 0)

/-- Proposition 4.1 of arXiv:1407.0085v2 (printed p. 9; proof in Section 4.2,
pp. 13–14), registered as a proposition.  For `0 < a,k < 1`, a known `k`-good
set `X` of size at most `⌈3 n^k log n⌉`, and `A` of size `⌈n^a⌉`, there is a
quantum algorithm with `Õ(n^{1/2+k} + n^{1/2+2a/3} + n^{1/2+a-k/2})` queries
that detects an edge of a triangle inside `Δ_G(X,A)` with probability at least
`2/3`.

`Õ` is represented by a constant, the three powers, and a polylog degree `d`.
The proof combines Lemma 4.2 (`m = n^k`) with the walk over
`J(A, ⌈n^{2a/3}⌉)`, Lemma 4.3, and Theorem 2.2 (MNRS); the walking cost is
`Õ(n^k + n^{2a/3} + √|Δ_G(X,A,w)|)` per `w` and Cauchy–Schwarz plus
`k`-goodness gives the displayed query bound (paper p. 14).

Proof status: statement registered, not proved in this layer.  The MNRS walk
instantiation on `J(A, ⌈n^{2a/3}⌉)` — setup `|A|·|X|`, update `2|X|`, checking
`√(|Δ_G(X,B,w)|)` from Lemma 4.2's estimate, summed with
`∑_w |Δ_G(X,A,w)| ≤ |A|² n^{1-k}` — has no repository formalization path yet.
Candidate reusable dependencies: `Qatlib.Concepts.WalkSearch.MnrsAmplify`
(MNRS walk guarantee and cost ledger) and `source_lemma_4_2`/`source_lemma_4_3`. -/
def source_proposition_4_1 : Prop :=
  ∀ (a k : ℝ), 0 < a → a < 1 → 0 < k → k < 1 →
    ∃ c d : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : TriangleCheckQuantumAlgorithm n,
        (A.queries : ℝ) ≤
            (c : ℝ) * (Real.rpow (n : ℝ) (1 / 2 + k) +
              Real.rpow (n : ℝ) (1 / 2 + 2 * a / 3) +
              Real.rpow (n : ℝ) (1 / 2 + a - k / 2)) *
              (Real.log (n : ℝ)) ^ d ∧
          ∀ (G : SimpleGraph (Fin n)) (X Aset : Finset (Fin n)),
            KGood G X k →
              (X.card : ℝ) ≤ 3 * Real.rpow (n : ℝ) k * Real.log (n : ℝ) →
                Aset.card = Nat.ceil (Real.rpow (n : ℝ) a) →
                  ContainsTriangleEdge G X Aset →
                    (2 : ℝ) / 3 ≤ A.acceptProbability G Aset

end Qatlib.Papers.TriangleFind14.MainResults
