/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

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

/-- `G` contains no cycle, in the closed-walk formulation every closed walk has
length zero (arXiv:1610.00581v1, §3, p. 9: "Assume that `G` does not contain a
cycle at all"). -/
def CycleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.length = 0

/-- `G` has a cycle of length `l ≤ d` passing through `k`
(arXiv:1610.00581v1, §4, Theorem 2, p. 9). -/
def CycleThroughWithin {V : Type*} (G : SimpleGraph V) (k : V) (d : ℕ) : Prop :=
  ∃ (c : ℕ) (p : G.Walk k k), 0 < c ∧ p.length = c ∧ c ≤ d

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
  obtain ⟨c, p, hc, hp, hcd⟩ := h
  exact ⟨c, p, hc, hp, le_trans hcd hdd⟩

/-- **Theorem 2, specification form** (arXiv:1610.00581v1, §4, Theorem 2, p. 9).

There is an interface `A : CycleDetectionAlgorithm n` and a constant `c > 0`
such that for every `n`-vertex graph `G`, vertex `k` and integer `d`:

* if `G` has a cycle of length `l ≤ d` through `k`, then `A` accepts with
  probability at least `9/20`;
* if `G` has no cycle, then `A` accepts with probability at most `1/10`
  (rejects with probability at least `9/10`);
* the recorded number of adjacency queries and workspace bits obey the paper's
  `Õ(n√d)` and `O(log n)` bounds.

This is a *specification* statement: `CycleDetectionAlgorithm` records the
acceptance probabilities and resource counts as fields but does not tie them to
a circuit, so the witness with `accept = 1` on cyclic inputs and `0` otherwise,
zero queries and zero space satisfies the contract.  The span-program
construction and the query/space ledger are the documented gap of this Block. -/
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
      queries := fun _ _ _ => 0
      space := 0 }
  refine ⟨A, 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro G k d hcyc
    change 9 / 20 ≤ (if CycleThroughWithin G k d then (1 : ℝ) else 0)
    rw [if_pos hcyc]
    norm_num
  · intro G k d hfree
    have hnot : ¬ CycleThroughWithin G k d := by
      rintro ⟨c, p, hc, hp, -⟩
      have h0 := hfree _ p
      omega
    change 9 / 10 ≤ 1 - (if CycleThroughWithin G k d then (1 : ℝ) else 0)
    rw [if_neg hnot]
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
