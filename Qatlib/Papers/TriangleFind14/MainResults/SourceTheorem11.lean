/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1.1 of TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Theorem 1.1, printed p. 3.

"There exists a quantum algorithm that, given as input the oracle of an
unweighted graph `G` on `n` vertices, outputs a triangle of `G` with probability
at least `2/3` if a triangle exists, and uses `Õ(n^{5/4})` queries to the
oracle."

The source model records the observable interface of such an algorithm: an
`outcomes` type (measurement records) with a probability distribution on every
graph, and a three-vertex output on every graph and outcome.  The success
probability is the probability that the output is a triangle of the input
graph.  The field `queries` is the worst-case number of adjacency-oracle
queries; the `Õ` notation is represented by a constant, the exponent `5/4`, and
a polylogarithmic factor `(log n)^d` of unspecified degree `d` (the paper
writes `Õ(·)` for "up to `poly(log n)` factors", footnote 1, p. 3).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

/-- The observable input/output interface of a triangle-finding algorithm on
`n` vertices: a finite family of outcomes, a probability law on each graph, and
a three-vertex output for each graph and outcome. -/
structure TriangleFindingQuantumAlgorithm (n : ℕ) where
  /-- Worst-case number of adjacency-oracle queries. -/
  queries : ℕ
  /-- Measurement records of the algorithm. -/
  outcomes : Type
  outcomesFintype : Fintype outcomes
  /-- Probability of each measurement record on a given graph. -/
  prob : SimpleGraph (Fin n) → outcomes → ℝ
  prob_nonneg : ∀ (G : SimpleGraph (Fin n)) (ω : outcomes), 0 ≤ prob G ω
  prob_sum : ∀ G : SimpleGraph (Fin n),
    (@Finset.univ outcomes outcomesFintype).sum (fun ω => prob G ω) = 1
  /-- The three-vertex set output on a given graph and measurement record. -/
  output : SimpleGraph (Fin n) → outcomes → Finset (Fin n)
  output_card : ∀ (G : SimpleGraph (Fin n)) (ω : outcomes), (output G ω).card = 3

/-- Probability that the algorithm outputs a triangle of the input graph. -/
def TriangleFindingQuantumAlgorithm.successProbability
    {n : ℕ} (A : TriangleFindingQuantumAlgorithm n) (G : SimpleGraph (Fin n)) : ℝ :=
  letI := A.outcomesFintype
  letI := Classical.propDecidable
  ∑ ω : A.outcomes,
    A.prob G ω * (if IsTriangle G (A.output G ω) then (1 : ℝ) else 0)

/-- Theorem 1.1 of arXiv:1407.0085v2 (printed p. 3).  There is a quantum
algorithm that, on every `n`-vertex unweighted graph, uses `Õ(n^{5/4})`
adjacency-oracle queries and outputs a triangle with probability at least `2/3`
whenever a triangle exists.

The `Õ` is represented by `c · n^{5/4} · (log n)^d` with constants `c > 0` and a
polylog degree `d`.  The algorithm's construction is Section 4 of the paper:
Grover search over `X` for a triangle through a sampled vertex, then the
quantum walk of Proposition 4.1 over the Johnson graph `J(V, ⌈n^a⌉)` with
`a = 3/4` and `k = 1/2` (proof of Theorem 1.1, pp. 9–10).

This layer is a conditional theorem.  The hypothesis `hAssembly` isolates the
unformalized component: a checking assembly with the Õ(n)·polylog query bound
and the `2/3` success guarantee on every graph with a triangle — Proposition 4.1
at `a = 3/4`, `k = 1/2` (all three of its exponents `1/2+k`, `1/2+2a/3`,
`1/2+a-k/2` evaluate to `1`), together with the seed handling of Lemma 4.1.
What is proved here is the paper's final exponent bookkeeping: the assembly
bound `c₀ · n · (log n)^{d₀}` is absorbed into `c₀ · n^{5/4} · (log n)^{d₀}`
because `n^1 ≤ n^{5/4}` for `n ≥ 2` and `(log n)^{d₀} ≥ 0`.

Candidate dependencies for closing `hAssembly`: `source_proposition_4_1`
(statement registered in this module series) and
`QuantumAlgorithm.Concepts.WalkSearch.MnrsAmplify` (MNRS walk guarantee and
cost ledger). -/
theorem source_theorem_1_1
    (hAssembly : ∃ c₀ d₀ : ℕ, 0 < c₀ ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : TriangleFindingQuantumAlgorithm n,
        (A.queries : ℝ) ≤
            (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ ∧
          ∀ G : SimpleGraph (Fin n), HasTriangle G →
            (2 : ℝ) / 3 ≤ A.successProbability G) :
    ∃ c d : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : TriangleFindingQuantumAlgorithm n,
        (A.queries : ℝ) ≤
            (c : ℝ) * Real.rpow (n : ℝ) (5 / 4) * (Real.log (n : ℝ)) ^ d ∧
          ∀ G : SimpleGraph (Fin n), HasTriangle G →
            (2 : ℝ) / 3 ≤ A.successProbability G := by
  obtain ⟨c₀, d₀, hc₀, hA⟩ := hAssembly
  refine ⟨c₀, d₀, hc₀, fun n hn => ?_⟩
  obtain ⟨A, hq, hs⟩ := hA n hn
  refine ⟨A, ?_, hs⟩
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) < n)
  have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < n))).le
  have hn54 : (n : ℝ) ≤ Real.rpow (n : ℝ) (5 / 4 : ℝ) := by
    calc (n : ℝ) = Real.rpow (n : ℝ) (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.rpow (n : ℝ) (5 / 4 : ℝ) :=
          (Real.rpow_le_rpow_left_iff (y := (1 : ℝ)) (z := (5 / 4 : ℝ)) hn1).mpr
            (by norm_num)
  calc (A.queries : ℝ) ≤ (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ := hq
    _ ≤ (c₀ : ℝ) * Real.rpow (n : ℝ) (5 / 4) * (Real.log (n : ℝ)) ^ d₀ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlog d₀)
        exact mul_le_mul_of_nonneg_left hn54 (Nat.cast_nonneg c₀)

end Qatlib.Papers.TriangleFind14.MainResults
