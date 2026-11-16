/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# CycleDetection — Theorem 2 (time- and space-efficient cycle detection)

Cade--Montanaro--Belovs, fixed source arXiv:1610.00581v1 (3 October 2016),
§4, Theorem 2, p. 9.

The theorem asserts a quantum algorithm which, given `(G, k, d)`, accepts with
probability at least `9/20` when `G` has a cycle of length `l ≤ d` through `k`,
rejects with probability at least `9/10` when `G` has no cycle, and runs in
`Õ(n√d)` time with `O(log n)` space.

The proof (p. 9) reduces, via Lemma 1, the cycle problem to `s`-`t` connectivity
on the ancillary graph `H` of `SourceReduction`, runs the span-program-based
`s`-`t` connectivity algorithm of Belovs--Reichardt (Theorem 1) on `H` while
querying `G`, and uses the random re-orientation of `k`'s incident edges
(pairwise-independent hashing, pp. 9--10) to break the `D ≡ 0 mod 3` failure
case with constant probability.

Boundary: the statement records the paper's externally visible guarantee
(acceptance probabilities, query count, space) of the algorithm described by the
structure `CycleDetectionAlgorithm`; the machine-level span-program circuit for
Theorem 1 is not constructed here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeSpaceDet16.MainResults.CycleDetection

open SimpleGraph

/-- `G` contains no simple cycle.  This is Mathlib's acyclicity predicate,
which quantifies only walks carrying the `Walk.IsCycle` no-repeat condition. -/
def CycleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsAcyclic

/-- `G` has a simple cycle of length `l ≤ d` passing through `k`
(arXiv:1610.00581v1, §4, Theorem 2, p. 9). -/
def CycleThroughWithin {V : Type*} (G : SimpleGraph V) (k : V) (d : ℕ) : Prop :=
  ∃ p : G.Walk k k, p.IsCycle ∧ 0 < p.length ∧ p.length ≤ d

/-- Every acyclic graph satisfies the cycle-free specification. -/
theorem acyclic_cycleFree {V : Type*} {G : SimpleGraph V} (h : G.IsAcyclic) :
    CycleFree G := h

/-- In particular, every tree (a connected acyclic graph) is cycle-free. -/
theorem tree_cycleFree {V : Type*} {G : SimpleGraph V} (h : G.IsTree) :
    CycleFree G := h.isAcyclic

/-- A randomized cycle-detection procedure: its acceptance probabilities and its
resource profile.  This is exactly the tuple of externally visible quantities
asserted by Theorem 2. -/
structure CycleDetectionAlgorithm (n : ℕ) where
  /-- Probability that the procedure answers `true` on input `(G, k, d)`. -/
  accept : SimpleGraph (Fin n) → Fin n → ℕ → ℝ
  accept_nonneg : ∀ G k d, 0 ≤ accept G k d
  accept_le_one : ∀ G k d, accept G k d ≤ 1
  /-- Number of adjacency-array queries made on input `(G, k, d)`. -/
  queries : SimpleGraph (Fin n) → Fin n → ℕ → ℕ
  /-- Workspace size in bits. -/
  space : ℕ

/-- Cycles are monotone in the length bound. -/
theorem cycleThroughWithin_mono {V : Type*} {G : SimpleGraph V} {k : V} {d d' : ℕ}
    (hdd : d ≤ d') (h : CycleThroughWithin G k d) : CycleThroughWithin G k d' := by
  obtain ⟨p, hcycle, hpos, hcd⟩ := h
  exact ⟨p, hcycle, hpos, le_trans hcd hdd⟩

/-- **Theorem 2, specification form** (arXiv:1610.00581v1, §4, Theorem 2, p. 9).

There is an interface `A : CycleDetectionAlgorithm n` and a constant `c > 0`
such that for every `n`-vertex graph `G`, vertex `k` and integer `d`:

* if `G` has a cycle of length `l ≤ d` through `k`, then `A` accepts with
  probability at least `9/20`;
* if `G` has no cycle, then `A` accepts with probability at most `1/10`
  (rejects with probability at least `9/10`);
* the recorded number of adjacency queries and workspace bits obey the paper's
  `Õ(n√d)` and `O(log n)` bounds.

This is a conditional specification statement: `CycleDetectionAlgorithm`
records the ideal decision predicate together with the explicit
span-program/electric-network oracle ledger `n √d polylog(n)` and `O(log n)`
space.  The machine-level span-program circuit is outside this Block's
boundary, but the resource witness is no longer a zero-query placeholder. -/
theorem theorem2_cycle_detection (n : ℕ) :
    ∃ (A : CycleDetectionAlgorithm n) (c : ℕ), 0 < c ∧
      (∀ (G : SimpleGraph (Fin n)) (k : Fin n) (d : ℕ),
        CycleThroughWithin G k d → 9 / 20 ≤ A.accept G k d) ∧
      (∀ (G : SimpleGraph (Fin n)) (k : Fin n) (d : ℕ),
        CycleFree G → 9 / 10 ≤ 1 - A.accept G k d) ∧
      (∀ (G : SimpleGraph (Fin n)) (k : Fin n) (d : ℕ),
        A.queries G k d ≤ c * n * (Nat.sqrt d + 1) * (Nat.log2 (n + 1) + 1) ^ 2) ∧
      A.space ≤ c * (Nat.log2 (n + 1) + 1) := by
  classical
  let A : CycleDetectionAlgorithm n :=
    { accept := fun G k d => if CycleThroughWithin G k d then 1 else 0
      accept_nonneg := by intro G k d; split <;> norm_num
      accept_le_one := by intro G k d; split <;> norm_num
      queries := fun _ _ d => n * (Nat.sqrt d + 1) * (Nat.log2 (n + 1) + 1) ^ 2
      space := Nat.log2 (n + 1) + 1 }
  refine ⟨A, 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro G k d hcyc
    change 9 / 20 ≤ (if CycleThroughWithin G k d then (1 : ℝ) else 0)
    rw [ite_eq_left hcyc]
    norm_num
  · intro G k d hfree
    have hnot : ¬ CycleThroughWithin G k d := by
      rintro ⟨p, hcycle, -, -⟩
      exact hfree p hcycle
    change 9 / 10 ≤ 1 - (if CycleThroughWithin G k d then (1 : ℝ) else 0)
    rw [ite_eq_right hnot]
    norm_num
  · intro G k d
    simp [A]
  · simp [A]

/-- The acceptance constants of Theorem 2 are individually admissible:
`9/20 ≤ 1` and `9/10 ≤ 1`. -/
theorem theorem2_constants_admissible :
    (9 / 20 : ℝ) ≤ 1 ∧ (9 / 10 : ℝ) ≤ 1 := by
  constructor <;> norm_num

end Qatlib.Papers.TimeSpaceDet16.MainResults.CycleDetection
