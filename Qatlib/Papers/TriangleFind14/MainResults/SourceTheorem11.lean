/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1.1 of TriangleFind14: an assembly cost contract

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Theorem 1.1, printed p. 3.

This file does not claim to construct the paper's quantum algorithm.  It gives an
honest interface for an oracle algorithm and proves the final exponent bookkeeping
from an assembly certificate.  A run carries a finite random seed, an explicit
edge-query transcript whose answers agree with the graph oracle, and an output that
is invariant under changing the graph without changing that transcript.  Thus the
query bound is tied to the transcript length and the output cannot inspect the graph
outside the recorded queries.

`source_theorem_1_1` is a conditional composition theorem.  Its hypothesis gives
separate `O(n polylog n)` bounds for the setup, walk/checking, and amplification
parts at the paper's parameters `a = 3/4`, `k = 1/2`, together with the assembled
algorithm's correctness.  The conclusion only adds those three costs and absorbs
`n ≤ n^(5/4)` for `n ≥ 2`; it does not assume an `O(n)` triangle-finding algorithm.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

/-- An unordered edge queried from an `n`-vertex graph. -/
abbrev EdgeQuery (n : ℕ) := Fin n × Fin n

/-- One oracle answer paired with the queried edge. -/
abbrev EdgeQueryAnswer (n : ℕ) := EdgeQuery n × Bool

/-- The Boolean answer supplied by the graph adjacency oracle. -/
noncomputable def edgeQueryAnswer {n : ℕ} (G : SimpleGraph (Fin n)) (e : EdgeQuery n) : Bool :=
  letI := Classical.propDecidable
  decide (G.Adj e.1 e.2)

/-- A finite-seed graph-oracle algorithm.

The transcript records every edge query and answer.  `trace_valid` ties those answers
to the graph oracle, `output_trace_invariant` prevents the output from using any
other graph information, and `trace_length_le` makes the query bound an actual
bound on the recorded transcript length. -/
structure TriangleFindingQuantumAlgorithm (n : ℕ) where
  /-- Finite random seed space for the measurement/randomness interface. -/
  Seed : Type
  seedFintype : Fintype Seed
  seedNonempty : Nonempty Seed
  /-- Oracle transcript produced on a graph and random seed. -/
  trace : SimpleGraph (Fin n) → Seed → List (EdgeQueryAnswer n)
  /-- Every answer in a transcript is the corresponding adjacency-oracle answer. -/
  trace_valid : ∀ (G : SimpleGraph (Fin n)) (r : Seed) (q : EdgeQueryAnswer n),
    q ∈ trace G r → q.2 = edgeQueryAnswer G q.1
  /-- Three-vertex output produced after the transcript. -/
  output : SimpleGraph (Fin n) → Seed → Finset (Fin n)
  output_card : ∀ (G : SimpleGraph (Fin n)) (r : Seed), (output G r).card = 3
  /-- The output depends on the graph only through the recorded transcript. -/
  output_trace_invariant : ∀ (G H : SimpleGraph (Fin n)) (r : Seed),
    trace G r = trace H r → output G r = output H r
  /-- Claimed worst-case query bound. -/
  queryBound : ℕ
  /-- The claimed bound is an upper bound on every transcript length. -/
  trace_length_le : ∀ (G : SimpleGraph (Fin n)) (r : Seed),
    (trace G r).length ≤ queryBound

/-- Compatibility projection for code that used the former `queries` field.  Its value is now the
transcript-derived `queryBound`, whose validity is supplied by `trace_length_le`. -/
abbrev TriangleFindingQuantumAlgorithm.queries {n : ℕ}
    (A : TriangleFindingQuantumAlgorithm n) : ℕ := A.queryBound

/-- Probability that the transcript-constrained algorithm outputs a triangle. -/
noncomputable def TriangleFindingQuantumAlgorithm.successProbability
    {n : ℕ} (A : TriangleFindingQuantumAlgorithm n) (G : SimpleGraph (Fin n)) : ℝ :=
  letI := A.seedFintype
  uniformProb (fun r : A.Seed => IsTriangle G (A.output G r))

/-- The setup, walk/checking, and amplification costs of one assembled run. -/
structure TriangleFindingAssembly (n : ℕ) where
  /-- The transcript-constrained assembled algorithm. -/
  algorithm : TriangleFindingQuantumAlgorithm n
  /-- Setup cost, corresponding to sampling and preparing the good set. -/
  setupCost : ℝ
  /-- Walk/checking cost, corresponding to Proposition 4.1. -/
  walkCost : ℝ
  /-- Amplification and final checking cost. -/
  amplificationCost : ℝ
  setup_nonneg : 0 ≤ setupCost
  walk_nonneg : 0 ≤ walkCost
  amplification_nonneg : 0 ≤ amplificationCost
  /-- The actual transcript query bound is paid for by the three subroutines. -/
  queryBound_le :
    (algorithm.queryBound : ℝ) ≤ setupCost + walkCost + amplificationCost

/-- Conditional exponent bookkeeping for Theorem 1.1.

The hypothesis supplies a transcript-constrained assembled algorithm and separate
`O(n (log n)^d)` bounds for its setup, walk/checking, and amplification costs.
The correctness clause is also supplied by the assembly certificate.  The proof combines
those costs and changes only the polynomial exponent from `1` to `5/4`. -/
theorem source_theorem_1_1
    (hAssembly : ∃ c₀ d₀ : ℕ, 0 < c₀ ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : TriangleFindingAssembly n,
        A.setupCost ≤ (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ ∧
          A.walkCost ≤ (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ ∧
          A.amplificationCost ≤ (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ ∧
          ∀ G : SimpleGraph (Fin n), HasTriangle G →
            (2 : ℝ) / 3 ≤ A.algorithm.successProbability G) :
    ∃ c d : ℕ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ A : TriangleFindingQuantumAlgorithm n,
        (A.queryBound : ℝ) ≤
            (c : ℝ) * Real.rpow (n : ℝ) (5 / 4) * (Real.log (n : ℝ)) ^ d ∧
          ∀ G : SimpleGraph (Fin n), HasTriangle G →
            (2 : ℝ) / 3 ≤ A.successProbability G := by
  obtain ⟨c₀, d₀, hc₀, hA⟩ := hAssembly
  refine ⟨3 * c₀, d₀, by omega, fun n hn => ?_⟩
  obtain ⟨A, hsetup, hwalk, hamp, hsuccess⟩ := hA n hn
  refine ⟨A.algorithm, ?_, hsuccess⟩
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : (1 : ℕ) < n)
  have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < n))).le
  have hsum : (A.algorithm.queryBound : ℝ) ≤
      3 * (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ := by
    calc
      (A.algorithm.queryBound : ℝ) ≤
          A.setupCost + A.walkCost + A.amplificationCost := A.queryBound_le
      _ ≤ (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ +
          (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ +
          (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ := by
            linarith
      _ = 3 * (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ := by ring
  have hn54 : (n : ℝ) ≤ Real.rpow (n : ℝ) (5 / 4 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.rpow (n : ℝ) (5 / 4 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (y := (1 : ℝ)) (z := (5 / 4 : ℝ)) hn1).mpr
          (by norm_num)
  calc
    (A.algorithm.queryBound : ℝ) ≤
        3 * (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ := hsum
    _ ≤ (3 * c₀ : ℝ) * Real.rpow (n : ℝ) (5 / 4) *
        (Real.log (n : ℝ)) ^ d₀ := by
          have hmul :
              3 * (c₀ : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ d₀ ≤
                3 * (c₀ : ℝ) * Real.rpow (n : ℝ) (5 / 4) *
                  (Real.log (n : ℝ)) ^ d₀ := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlog d₀)
            exact mul_le_mul_of_nonneg_left hn54 (by positivity)
          exact hmul
    _ = ((3 * c₀ : ℕ) : ℝ) * Real.rpow (n : ℝ) (5 / 4) *
        (Real.log (n : ℝ)) ^ d₀ := by
          norm_num [Nat.cast_mul]

end Qatlib.Papers.TriangleFind14.MainResults
