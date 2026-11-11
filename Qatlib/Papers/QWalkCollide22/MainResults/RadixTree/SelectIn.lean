/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# The radix-tree rank/select primitive of Section 5

Fixed version: arXiv:2205.14023, *Finding many Collisions via Reusable Quantum
Walks*, Section 5 ("Data structure"), pp.15–17, and Appendix Algorithm 6.

The data structure of Section 5 stores `S ⊆ {0,1}^n` in a binary trie whose
leaves are the `2^n` binary strings `0…0, …, 1…1` in lexicographic (i.e.
numeric) order.  Two primitives are used by the algorithm:

* `countIn S lo len` — the number of stored keys in the interval
  `[lo, lo + len)` (the "rank" primitive: how many keys lie in a subtree);
* `selectIn S n lo i` — the `i`-th smallest key of `[lo, lo + 2^n) \ S` (the
  "select" primitive, Appendix Algorithm 6 `findNthNotInTree`), obtained by
  descending the trie and skipping a subtree when it is full.

This file defines both primitives and proves the two facts used by Theorem 7:
`selectIn_spec` (select returns the element of the required rank which is not
in `S`) and `visitCount_le` (the descent visits at most one trie node per
level, i.e. `O(n)` nodes, hence `O(n^2)` bit operations).

Everything is stated for the `ℕ`-model `[0, 2^n)` of `{0,1}^n`, matching the
numeric order of the trie leaves.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QWalkCollide22.MainResults

/-- `countIn S lo len` is the number of stored elements of `S` in the integer
interval `[lo, lo + len)`.  In the trie of Section 5, `countIn S lo (2^j)`
counts the keys of `S` lying in the subtree rooted at the node whose binary
prefix is given by `lo` (with `j` remaining levels). -/
def countIn (S : Finset ℕ) (lo len : ℕ) : ℕ :=
  (S.filter (fun x => lo ≤ x ∧ x < lo + len)).card

/-- **Rank bound (Section 5, p.15).**  A subtree of `len` leaves contains at
most `len` stored keys. -/
lemma countIn_le (S : Finset ℕ) (lo len : ℕ) : countIn S lo len ≤ len := by
  unfold countIn
  calc (S.filter (fun x => lo ≤ x ∧ x < lo + len)).card
      ≤ (Finset.Ico lo (lo + len)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
        exact ⟨hx.2.1, hx.2.2⟩
    _ = len := by rw [Nat.card_Ico]; omega

/-- **Additivity of the rank primitive (Section 5, p.15).**  Splitting an
interval at its midpoint splits the count into the two children. -/
lemma countIn_add (S : Finset ℕ) (lo a b : ℕ) :
    countIn S lo (a + b) = countIn S lo a + countIn S (lo + a) b := by
  unfold countIn
  rw [show lo + (a + b) = lo + a + b by omega]
  have hdisj : Disjoint (S.filter (fun x => lo ≤ x ∧ x < lo + a))
      (S.filter (fun x => lo + a ≤ x ∧ x < lo + a + b)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    omega
  have hunion : S.filter (fun x => lo ≤ x ∧ x < lo + a + b) =
      S.filter (fun x => lo ≤ x ∧ x < lo + a) ∪
        S.filter (fun x => lo + a ≤ x ∧ x < lo + a + b) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxS, h1, h2⟩
      by_cases h : x < lo + a
      · exact Or.inl ⟨hxS, h1, h⟩
      · exact Or.inr ⟨hxS, by omega, h2⟩
    · rintro (⟨hxS, h1, h2⟩ | ⟨hxS, h1, h2⟩)
      · exact ⟨hxS, h1, by omega⟩
      · exact ⟨hxS, by omega, h2⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- **Rank of the complement of a full interval (Section 5, p.15).**  The
interval `[lo, lo + len)` has exactly `len - countIn S lo len` leaves that are
*not* occupied by `S`. -/
lemma card_interval_filter_notMem (S : Finset ℕ) (lo len : ℕ) :
    ((Finset.Ico lo (lo + len)).filter (fun z => z ∉ S)).card
      = len - countIn S lo len := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Ico lo (lo + len))
    (p := fun z => z ∈ S)
  have hcard : (Finset.Ico lo (lo + len)).card = len := by
    rw [Nat.card_Ico]; omega
  have hfil : ((Finset.Ico lo (lo + len)).filter (fun z => z ∈ S)).card
      = countIn S lo len := by
    rw [countIn]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico]
    tauto
  omega

/-- **Select (Appendix, Algorithm 6 `findNthNotInTree`; Section 5, p.16).**
`selectIn S n lo i` returns the `i`-th smallest element of the complement of
`S` inside `[lo, lo + 2^n)`.  At a node with `n+1` remaining levels, the left
child covers `[lo, lo + 2^n)` and contains `countIn S lo (2^n)` keys, hence
`2^n - countIn S lo (2^n)` free leaves; if `i` is smaller than this number the
answer lies in the left child, otherwise we descend right and subtract it.
At a leaf (`n = 0`) the only element is `lo`.

The `i`-th element of the complement exists precisely when
`i < 2^n - countIn S lo (2^n)`; `selectIn_spec` states the correctness on that
domain. -/
def selectIn (S : Finset ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, i =>
      if i < 2 ^ fuel - countIn S lo (2 ^ fuel) then
        selectIn S fuel lo i
      else
        selectIn S fuel (lo + 2 ^ fuel)
          (i - (2 ^ fuel - countIn S lo (2 ^ fuel)))

/-- Defining equation of `selectIn` at a leaf. -/
lemma selectIn_zero (S : Finset ℕ) (lo i : ℕ) : selectIn S 0 lo i = lo := rfl

/-- Defining equation of `selectIn` at an internal node. -/
lemma selectIn_succ (S : Finset ℕ) (fuel lo i : ℕ) :
    selectIn S (fuel + 1) lo i =
      if i < 2 ^ fuel - countIn S lo (2 ^ fuel) then
        selectIn S fuel lo i
      else
        selectIn S fuel (lo + 2 ^ fuel)
          (i - (2 ^ fuel - countIn S lo (2 ^ fuel))) := rfl

/-- **Correctness of select (Appendix, Algorithm 6; Section 5, p.16).**
For `i < 2^n - countIn S lo (2^n)`, `selectIn S n lo i` is an element of
`[lo, lo + 2^n)` which is not in `S`, and it is the `i`-th such element: the
number of free leaves of `[lo, selectIn S n lo i)` is exactly `i`.

This is the invariant maintained by the descent.  The paper states it for the
root `lo = 0`, `n` levels (Lemma in Section 5); we prove the general
sub-interval form needed by the induction, which specialises to
`findNthNotInTree_spec` in `Theorem7.lean`. -/
theorem selectIn_spec (S : Finset ℕ) :
    ∀ fuel lo i, i < 2 ^ fuel - countIn S lo (2 ^ fuel) →
      lo ≤ selectIn S fuel lo i ∧
      selectIn S fuel lo i < lo + 2 ^ fuel ∧
      selectIn S fuel lo i ∉ S ∧
      ((Finset.Ico lo (selectIn S fuel lo i)).filter
        (fun z => z ∉ S)).card = i := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo i hi
      rw [selectIn_zero]
      simp only [pow_zero] at hi ⊢
      have hcle : countIn S lo 1 ≤ 1 := countIn_le S lo 1
      have hi0 : i = 0 := by omega
      have hnotmem : lo ∉ S := by
        intro hlo
        have hpos : 0 < countIn S lo 1 := by
          rw [countIn]
          exact Finset.card_pos.mpr ⟨lo, by simp [hlo]⟩
        omega
      exact ⟨le_rfl, by omega, hnotmem, by simp [hi0]⟩
  | succ fuel ih =>
      intro lo i hi
      rw [selectIn_succ]
      set cl : ℕ := countIn S lo (2 ^ fuel) with hcl
      have hpow2 : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by
        rw [pow_succ]; ring
      have hsplit : countIn S lo (2 ^ fuel + 2 ^ fuel) =
          cl + countIn S (lo + 2 ^ fuel) (2 ^ fuel) := by
        have h := countIn_add S lo (2 ^ fuel) (2 ^ fuel)
        simpa [hcl] using h
      have htotal : i < 2 ^ fuel + 2 ^ fuel -
          (cl + countIn S (lo + 2 ^ fuel) (2 ^ fuel)) := by
        have h := hi
        rw [hpow2, hsplit] at h
        exact h
      have hcl_le : cl ≤ 2 ^ fuel := countIn_le S lo (2 ^ fuel)
      have hcr_le : countIn S (lo + 2 ^ fuel) (2 ^ fuel) ≤ 2 ^ fuel :=
        countIn_le S (lo + 2 ^ fuel) (2 ^ fuel)
      by_cases hbranch : i < 2 ^ fuel - cl
      · rw [if_pos hbranch]
        obtain ⟨i1, i2, i3, i4⟩ := ih lo i (by simpa [hcl] using hbranch)
        rw [hpow2]
        exact ⟨i1, by omega, i3, i4⟩
      · rw [if_neg hbranch]
        push Not at hbranch
        rw [hpow2]
        have ihb : i - (2 ^ fuel - cl) <
            2 ^ fuel - countIn S (lo + 2 ^ fuel) (2 ^ fuel) := by omega
        obtain ⟨h1, h2', h3, h4⟩ := ih (lo + 2 ^ fuel) (i - (2 ^ fuel - cl)) ihb
        refine ⟨by omega, by omega, h3, ?_⟩
        have hdec : Finset.Ico lo (selectIn S fuel (lo + 2 ^ fuel)
              (i - (2 ^ fuel - cl))) =
            Finset.Ico lo (lo + 2 ^ fuel) ∪
              Finset.Ico (lo + 2 ^ fuel) (selectIn S fuel (lo + 2 ^ fuel)
                (i - (2 ^ fuel - cl))) := by
          rw [Finset.Ico_union_Ico_eq_Ico (by omega) h1]
        have hdisj : Disjoint (Finset.Ico lo (lo + 2 ^ fuel))
            (Finset.Ico (lo + 2 ^ fuel) (selectIn S fuel (lo + 2 ^ fuel)
              (i - (2 ^ fuel - cl)))) := by
          rw [Finset.disjoint_left]
          intro z hz hz'
          simp only [Finset.mem_Ico] at hz hz'
          omega
        have hdisj' : Disjoint ((Finset.Ico lo (lo + 2 ^ fuel)).filter
              (fun z => z ∉ S))
            ((Finset.Ico (lo + 2 ^ fuel) (selectIn S fuel (lo + 2 ^ fuel)
              (i - (2 ^ fuel - cl)))).filter (fun z => z ∉ S)) := by
          rw [Finset.disjoint_left]
          intro z hz hz'
          simp only [Finset.mem_filter] at hz hz'
          exact (Finset.disjoint_left.mp hdisj) hz.1 hz'.1
        rw [hdec, Finset.filter_union, Finset.card_union_of_disjoint hdisj']
        have hbase : ((Finset.Ico lo (lo + 2 ^ fuel)).filter
            (fun z => z ∉ S)).card = 2 ^ fuel - cl := by
          simpa [hcl] using card_interval_filter_notMem S lo (2 ^ fuel)
        rw [hbase, h4]
        omega

/-- **Visited nodes of the select descent (Section 5, p.16).**  `visitCount`
counts the trie nodes inspected by `selectIn`: one per level plus the leaf.
It follows exactly the same branching as `selectIn`. -/
def visitCount (S : Finset ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | fuel + 1, lo, i =>
      if i < 2 ^ fuel - countIn S lo (2 ^ fuel) then
        1 + visitCount S fuel lo i
      else
        1 + visitCount S fuel (lo + 2 ^ fuel)
          (i - (2 ^ fuel - countIn S lo (2 ^ fuel)))

/-- **Select runs in `O(n)` node visits (Section 5, p.16; Theorem 7).**  The
descent inspects at most one node per trie level, i.e. at most `n + 1` nodes,
so with `O(n)`-bit labels the running time is `O(n^2) = O(n^2)` bit
operations — linear in the `O(n^2)`-bit input/output, as claimed in Theorem 7.
-/
theorem visitCount_le (S : Finset ℕ) :
    ∀ fuel lo i, visitCount S fuel lo i ≤ fuel + 1 := by
  intro fuel
  induction fuel with
  | zero => intro lo i; simp only [visitCount]; omega
  | succ fuel ih =>
      intro lo i
      simp only [visitCount]
      split
      · have h := ih lo i; omega
      · have h := ih (lo + 2 ^ fuel)
            (i - (2 ^ fuel - countIn S lo (2 ^ fuel))); omega

end Qatlib.Papers.QWalkCollide22.MainResults
