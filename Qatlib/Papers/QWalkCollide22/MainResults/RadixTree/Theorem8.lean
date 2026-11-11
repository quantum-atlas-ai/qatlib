/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkCollide22.MainResults.RadixTree.Theorem7

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 8: `FindNthNotInTwoTrees` returns the `i`-th element outside two trees

Fixed version: arXiv:2205.14023, *Finding many Collisions via Reusable Quantum
Walks*, Theorem 8, page 33 (Section 5, Appendix Algorithm 8).

Paper statement:

> Theorem 8.  `FindNthNotInTwoTrees(i, T, T')` returns the `i`th element in
> `{0,1}^n \ (T ∪ T')` in `poly(n)` time.

The paper assumes that `T` and `T'` have disjoint leaves; this is the situation
in the chained quantum walk of Section 4, where the two trees hold
respectively the already-found collisions and the currently marked set.  The
implementation `findNthNotInTwoTrees n i S S'` is `FindNthNotInTree` run on the
merged tree `S ∪ S'` (the paper's `T ∪ T'`), so its correctness and complexity
both reduce to Theorem 7.

The joint hypothesis `hdisj : Disjoint S S'` is the paper's disjointness
assumption; `hS`, `hS'` say both leaf sets lie in `{0,1}^n`, and
`hi : i < 2^n - |S ∪ S'|` is the validity condition for the index. -/

set_option autoImplicit false

namespace Qatlib.Papers.QWalkCollide22.MainResults

/-- `findNthNotInTwoTrees n i S S'` is Algorithm 8 `FindNthNotInTwoTrees`:
the `i`-th smallest element of `{0,1}^n \ (S ∪ S')`, computed by the radix-tree
select procedure on the union of the two trees. -/
def findNthNotInTwoTrees (n i : ℕ) (S S' : Finset ℕ) : ℕ :=
  findNthNotInTree n i (S ∪ S')

/-- **Theorem 8** (arXiv:2205.14023, p.33, Appendix Algorithm 8).

For two trees with disjoint leaves `S, S' ⊆ {0,1}^n` and a valid index
`i < 2^n - |S ∪ S'|`, `FindNthNotInTwoTrees(i, T, T')` returns the `i`-th
element of `{0,1}^n \ (S ∪ S')` — i.e. it lies in `[0, 2^n)`, belongs to
neither `S` nor `S'`, and exactly `i` elements of `[0, 2^n) \ (S ∪ S')` are
smaller — in polynomial time: at most `n + 1` node visits and
`(n+1)(2n+1) = O(n^2)` bit operations. -/
theorem theorem_eight (n i : ℕ) (S S' : Finset ℕ)
    (hS : ∀ x ∈ S, x < 2 ^ n) (hS' : ∀ x ∈ S', x < 2 ^ n)
    (_hdisj : Disjoint S S') (hi : i < 2 ^ n - (S ∪ S').card) :
    findNthNotInTwoTrees n i S S' < 2 ^ n ∧
    findNthNotInTwoTrees n i S S' ∉ S ∧
    findNthNotInTwoTrees n i S S' ∉ S' ∧
    ((Finset.Ico 0 (findNthNotInTwoTrees n i S S')).filter
      (fun z => z ∉ S ∪ S')).card = i ∧
    visitCount (S ∪ S') n 0 i ≤ n + 1 ∧
    visitCount (S ∪ S') n 0 i * (2 * n + 1) ≤ selectBitOps n := by
  have hU : ∀ x ∈ S ∪ S', x < 2 ^ n := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hS x h
    · exact hS' x h
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_seven n i (S ∪ S') hU hi
  refine ⟨by simpa [findNthNotInTwoTrees] using h1, ?_, ?_,
    by simpa [findNthNotInTwoTrees] using h3,
    by simpa [findNthNotInTwoTrees] using h4,
    by simpa [findNthNotInTwoTrees] using h5⟩
  · intro h
    refine h2 ?_
    rw [Finset.mem_union]
    exact Or.inl h
  · intro h
    refine h2 ?_
    rw [Finset.mem_union]
    exact Or.inr h

end Qatlib.Papers.QWalkCollide22.MainResults
