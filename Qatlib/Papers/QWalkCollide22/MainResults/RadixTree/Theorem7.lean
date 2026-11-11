/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkCollide22.MainResults.RadixTree.SelectIn

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 7: `FindNthNotInTree` returns the `i`-th element outside a radix tree

Fixed version: arXiv:2205.14023, *Finding many Collisions via Reusable Quantum
Walks*, Theorem 7, page 33 (Section 5, Appendix Algorithm 7).

Paper statement:

> Theorem 7.  `FindNthNotInTree(i, T)` returns the `i`th element in `{0,1}^n \ T`
> in `poly(n)` time.

The radix tree `T` stores a set `S ⊆ {0,1}^n`; in the `ℕ`-model its leaves are
`[0, 2^n)` in lexicographic (numeric) order.  `findNthNotInTree n i S` is the
iteration of the trie descent `selectIn` from the root (`selectIn` in
`SelectIn.lean`).  The theorem below states:

* correctness — the returned value lies in `[0, 2^n) \ S` and is the `i`-th
  such value (exactly `i` elements of `[0, 2^n) \ S` are smaller);
* `poly(n)` time — the descent visits at most `n + 1` trie nodes, and with
  `O(n)`-bit labels at each node the total bit-operation count is at most
  `(n+1)(2n+1) = O(n^2)`, a polynomial in `n`.

The hypothesis `hS : ∀ x ∈ S, x < 2^n` says that `T`'s leaves lie in the
universe `{0,1}^n`, and `hi : i < 2^n - S.card` is the domain on which the
`i`-th element of the complement exists (`i < φ(2^n) - |T|` in the paper's
notation). -/

set_option autoImplicit false

namespace Qatlib.Papers.QWalkCollide22.MainResults

/-- `findNthNotInTree n i S` is Algorithm 7 `FindNthNotInTree(i, T)` of the
appendix: the `i`-th smallest element of `{0,1}^n \ S`, obtained by descending
the radix tree from the root. -/
def findNthNotInTree (n i : ℕ) (S : Finset ℕ) : ℕ :=
  selectIn S n 0 i

/-- A coarse bit-operation budget for one `FindNthNotInTree` call on `n`-bit
labels: at most `n + 1` visited nodes, each costing at most `2n + 1` bit
operations (an `n`-bit comparison plus a count subtraction). -/
def selectBitOps (n : ℕ) : ℕ := (n + 1) * (2 * n + 1)

/-- The rank primitive at the root is the cardinality of `S`, provided all
leaves of `S` lie in the universe `[0, 2^n)`. -/
lemma countIn_root (S : Finset ℕ) (n : ℕ) (hS : ∀ x ∈ S, x < 2 ^ n) :
    countIn S 0 (2 ^ n) = S.card := by
  unfold countIn
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, -, -⟩
    exact hx
  · intro hx
    exact ⟨hx, Nat.zero_le _, by have := hS x hx; omega⟩

/-- **Correctness of `FindNthNotInTree` (Theorem 7).**  For a tree `S` with
leaves in `[0, 2^n)` and a valid index `i < 2^n - |S|`, the value returned by
`findNthNotInTree n i S` is exactly the `i`-th element of `{0,1}^n \ S`:
it lies in `[0, 2^n)`, is not in `S`, and precisely `i` elements of
`[0, 2^n) \ S` are smaller than it. -/
theorem findNthNotInTree_spec (n i : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < 2 ^ n) (hi : i < 2 ^ n - S.card) :
    findNthNotInTree n i S < 2 ^ n ∧
    findNthNotInTree n i S ∉ S ∧
    ((Finset.Ico 0 (findNthNotInTree n i S)).filter
      (fun z => z ∉ S)).card = i := by
  have hcount : countIn S 0 (2 ^ n) = S.card := countIn_root S n hS
  have hi' : i < 2 ^ n - countIn S 0 (2 ^ n) := by rw [hcount]; exact hi
  have h := selectIn_spec S n 0 i hi'
  exact ⟨by simpa [findNthNotInTree] using h.2.1,
    by simpa [findNthNotInTree] using h.2.2.1,
    by simpa [findNthNotInTree] using h.2.2.2⟩

/-- **Theorem 7** (arXiv:2205.14023, p.33, Appendix Algorithm 7).

`FindNthNotInTree(i, T)` returns the `i`th element of `{0,1}^n \ T` and runs
in polynomial time: the descent visits at most `n + 1` radix-tree nodes and
performs at most `(n+1)(2n+1)` bit operations, both polynomial in the input
size `n` (the paper's `poly(n)`).

All hypotheses are the paper's: `S` is the leaf set of `T`, all its leaves lie
in `{0,1}^n` (`hS`), and `i` is a valid index into the complement
(`hi : i < 2^n - |S|`). -/
theorem theorem_seven (n i : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < 2 ^ n) (hi : i < 2 ^ n - S.card) :
    findNthNotInTree n i S < 2 ^ n ∧
    findNthNotInTree n i S ∉ S ∧
    ((Finset.Ico 0 (findNthNotInTree n i S)).filter
      (fun z => z ∉ S)).card = i ∧
    visitCount S n 0 i ≤ n + 1 ∧
    visitCount S n 0 i * (2 * n + 1) ≤ selectBitOps n := by
  obtain ⟨h1, h2, h3⟩ := findNthNotInTree_spec n i S hS hi
  have hv : visitCount S n 0 i ≤ n + 1 := visitCount_le S n 0 i
  exact ⟨h1, h2, h3, hv, Nat.mul_le_mul_right (2 * n + 1) hv⟩

end Qatlib.Papers.QWalkCollide22.MainResults
