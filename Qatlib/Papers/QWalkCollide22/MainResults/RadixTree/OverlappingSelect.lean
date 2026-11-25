/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalkCollide22.MainResults.RadixTree.Theorem8

@[expose] public section

/-!
# Complement selection on a merged leaf set

Theorem 8 of arXiv:2205.14023v1 assumes disjoint leaves. The existing Lean
consumer performs selection on the union, which supports overlapping leaves.
The node count is for selection on that union. The two-tree interval count
printed in Algorithm 10 can instead double-count a shared leaf.
-/

set_option autoImplicit false

open Qatlib.Papers.QWalkCollide22.MainResults

namespace Qatlib.Papers.QWalkCollide22.MainResults

/-- The merged implementation returns the complement rank and its selection bounds
for any two valid leaf sets, including overlap. -/
theorem theorem_eight_merged (n i : ℕ) (S S' : Finset ℕ)
    (hS : ∀ x ∈ S, x < 2 ^ n) (hS' : ∀ x ∈ S', x < 2 ^ n)
    (hi : i < 2 ^ n - (S ∪ S').card) :
    findNthNotInTwoTrees n i S S' < 2 ^ n ∧
    findNthNotInTwoTrees n i S S' ∉ S ∧ findNthNotInTwoTrees n i S S' ∉ S' ∧
    ((Finset.Ico 0 (findNthNotInTwoTrees n i S S')).filter
      (fun z => z ∉ S ∪ S')).card = i ∧
    visitCount (S ∪ S') n 0 i ≤ n + 1 ∧
    visitCount (S ∪ S') n 0 i * (2 * n + 1) ≤ selectBitOps n := by
  have hU (x : ℕ) (hx : x ∈ S ∪ S') : x < 2 ^ n :=
    (Finset.mem_union.mp hx).elim (hS x) (hS' x)
  obtain ⟨hrange, hexclude, hrank, hvisit, hcost⟩ := theorem_seven n i (S ∪ S') hU hi
  have hne := not_or.mp (Finset.mem_union.not.mp hexclude)
  exact ⟨hrange, hne.1, hne.2, hrank, hvisit, hcost⟩

/-- The internal-node subtraction in Algorithm 10, expressed on the interval's leaf sets. -/
def twoTreeIntervalCount (lo hi : ℕ) (S S' : Finset ℕ) : ℕ :=
  ((Finset.Ico lo hi).filter (fun z => z ∉ S')).card -
    ((Finset.Ico lo hi).filter (fun z => z ∈ S)).card

/-- At the root with leaves 0 and 2, a shared leaf 0 makes Algorithm 10's
interval subtraction give zero although the interval still contains the free leaf 1. -/
theorem twoTreeIntervalCount_overlap :
    twoTreeIntervalCount 0 2 ({0, 2} : Finset ℕ) {0} = 0 ∧
      ((Finset.Ico 0 (2 : ℕ)).filter (fun z => z ∉ ({0, 2} : Finset ℕ) ∪ {0})).card = 1 := by
  decide

end Qatlib.Papers.QWalkCollide22.MainResults
