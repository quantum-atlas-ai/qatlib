/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-!
# Addressed trees with cached squared norms

The leaves store signed entries. Each internal node caches the sum of its two children's
squared masses. A point write follows the address from the root and rebuilds that path,
sharing the sibling at each level. The write counter charges one cell for each rebuilt node
and the leaf. Each vacant subtree represents a whole zero interval without materializing
its leaves. A dense initialization is also available.

This is the sum tree used in [KerenidisPrakash2017], Appendix A,
[KerenidisLandmanPrakash2020], Appendix F.2, and [ChenXueChenEtAl2022], Appendix E.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Foundations.QramData.SquaredNormTree

/-- A binary address with the bit at index zero selecting the root's child. -/
abbrev Address (depth : ℕ) := Fin depth → Bool

/-- A binary tree with implicit zero intervals and cached masses at internal nodes. -/
inductive Tree (R : Type*) : ℕ → Type _
  | vacant (depth : ℕ) : Tree R depth
  | leaf (entry : R) : Tree R 0
  | node {depth : ℕ} (cachedMass : R) (left right : Tree R depth) : Tree R (depth + 1)

variable {R : Type*} [Semiring R] {depth : ℕ}

/-- Read a cached internal mass, or square the entry at a leaf. -/
def mass : Tree R depth → R
  | .vacant _ => 0
  | .leaf entry => entry ^ 2
  | .node cachedMass _ _ => cachedMass

/-- Construct a branch and cache the sum of the child masses. -/
def branch (left right : Tree R depth) : Tree R (depth + 1) :=
  .node (mass left + mass right) left right

/-- Every internal cache equals the sum of the child masses. -/
def Valid : {depth : ℕ} → Tree R depth → Prop
  | _, .vacant _ => True
  | _, .leaf _ => True
  | _, .node cachedMass left right =>
      cachedMass = mass left + mass right ∧ Valid left ∧ Valid right

/-- The signed entry in a depth-zero tree. -/
def leafEntry : Tree R 0 → R
  | .vacant _ => 0
  | .leaf entry => entry

/-- Inspect the selected child. A vacant node has two vacant children. -/
def child : Tree R (depth + 1) → Bool → Tree R depth
  | .vacant _, _ => .vacant depth
  | .node _ left right, bit => if bit then right else left

/-- Each child of a valid tree has consistent caches. -/
theorem valid_child (tree : Tree R (depth + 1)) (bit : Bool) (h : Valid tree) :
    Valid (child tree bit) := by
  cases tree with
  | vacant => trivial
  | node _ _ _ =>
      cases bit with
      | false => exact h.2.1
      | true => exact h.2.2

/-- The cached mass of a valid branch is the sum of its child masses. -/
theorem mass_eq_children (tree : Tree R (depth + 1)) (h : Valid tree) :
    mass tree = mass (child tree false) + mass (child tree true) := by
  cases tree with
  | vacant => simp [mass, child]
  | node _ _ _ => exact h.1

/-- At depth zero, the cached mass is the square of the stored entry. -/
theorem mass_eq_leaf (tree : Tree R 0) : mass tree = leafEntry tree ^ 2 := by
  cases tree <;> simp [mass, leafEntry]

/-- Read an individual signed entry by following its address. -/
def read : {depth : ℕ} → Tree R depth → Address depth → R
  | 0, tree, _ => leafEntry tree
  | _ + 1, tree, address => read (child tree (address 0)) (Fin.tail address)

/-- Initialize the tree from its addressed entries, building each child once. -/
def ofFn : (depth : ℕ) → (Address depth → R) → Tree R depth
  | 0, entries => .leaf (entries Fin.elim0)
  | depth + 1, entries =>
      branch (ofFn depth (fun suffix => entries (Fin.cons false suffix)))
        (ofFn depth (fun suffix => entries (Fin.cons true suffix)))

/-- The tree initialized from a function has consistent caches. -/
theorem valid_ofFn (depth : ℕ) (entries : Address depth → R) : Valid (ofFn depth entries) := by
  induction depth with
  | zero => trivial
  | succ depth ih =>
      exact ⟨rfl, ih _, ih _⟩

/-- Initialization preserves every individual entry. -/
@[simp] theorem read_ofFn (depth : ℕ) (entries : Address depth → R) (address : Address depth) :
    read (ofFn depth entries) address = entries address := by
  induction depth with
  | zero => exact congrArg entries (Subsingleton.elim _ _)
  | succ depth ih =>
      have rebuild := Fin.cons_self_tail address
      cases hb : address 0 <;>
        simp [ofFn, branch, child, read, hb, ih] <;>
        exact congrArg entries (by simpa [hb] using rebuild)

/-- Write a leaf, rebuild its ancestors, and count the cells written. -/
def writeWithCount : {depth : ℕ} → Tree R depth → Address depth → R → Tree R depth × ℕ
  | 0, _, _, entry => (.leaf entry, 1)
  | _ + 1, tree, address, entry =>
      let result := writeWithCount (child tree (address 0)) (Fin.tail address) entry
      let updated := if address 0 then branch (child tree false) result.1
        else branch result.1 (child tree true)
      (updated, result.2 + 1)

/-- Write an entry, returning the tree with its caches refreshed. -/
def write (tree : Tree R depth) (address : Address depth) (entry : R) : Tree R depth :=
  (writeWithCount tree address entry).1

/-- A point write stores precisely one cell per level, including the leaf. -/
@[simp] theorem write_cell_count (tree : Tree R depth) (address : Address depth) (entry : R) :
    (writeWithCount tree address entry).2 = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [writeWithCount, ih]

/-- Point writes preserve all cache invariants. -/
theorem valid_write (tree : Tree R depth) (address : Address depth) (entry : R)
    (h : Valid tree) : Valid (write tree address entry) := by
  induction depth with
  | zero => trivial
  | succ depth ih =>
      have hSub := ih (child tree (address 0)) (Fin.tail address)
        (valid_child tree (address 0) h)
      cases hb : address 0
      · simpa [write, writeWithCount, hb, branch, Valid] using
          And.intro hSub (valid_child tree true h)
      · simpa [write, writeWithCount, hb, branch, Valid] using
          And.intro (valid_child tree false h) hSub

/-- A write changes exactly the entry at its address. -/
theorem read_write (tree : Tree R depth) (address selected : Address depth) (entry : R) :
    read (write tree selected entry) address =
      if address = selected then entry else read tree address := by
  induction depth with
  | zero =>
      have h : address = selected := Subsingleton.elim _ _
      simp [write, writeWithCount, read, leafEntry, h]
  | succ depth ih =>
      have eq_iff : address = selected ↔
          address 0 = selected 0 ∧ Fin.tail address = Fin.tail selected := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨hHead, hTail⟩
          calc
            address = Fin.cons (address 0) (Fin.tail address) := (Fin.cons_self_tail _).symm
            _ = Fin.cons (selected 0) (Fin.tail selected) := by rw [hHead, hTail]
            _ = selected := Fin.cons_self_tail _
      have hWrite := ih (child tree (selected 0)) (Fin.tail address) (Fin.tail selected)
      cases ha : address 0 <;> cases hs : selected 0 <;>
        simp [write, writeWithCount, branch, read, child, ha, hs, eq_iff] at hWrite ⊢ <;>
        assumption

/-- The root of a valid tree stores the sum of the squared entries over all addresses. -/
theorem mass_eq_sum (tree : Tree R depth) (h : Valid tree) :
    mass tree = ∑ address : Address depth, read tree address ^ 2 := by
  induction depth with
  | zero =>
      let _ : Unique (Address 0) := ⟨⟨Fin.elim0⟩, fun _ => Subsingleton.elim _ _⟩
      simp [mass_eq_leaf, read]
  | succ depth ih =>
      rw [mass_eq_children tree h, ih _ (valid_child tree false h), ih _ (valid_child tree true h)]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (depth + 1) => Bool))
        (fun pair => read tree (Fin.cons pair.1 pair.2) ^ 2)
        (fun address => read tree address ^ 2) (fun _ => rfl)]
      simp [Fintype.sum_prod_type, read, add_comm]

/-- Count materialized value and cache cells. Vacant intervals carry no payload. -/
def storedCells : {depth : ℕ} → Tree R depth → ℕ
  | _, .vacant _ => 0
  | _, .leaf _ => 1
  | _, .node _ left right => storedCells left + storedCells right + 1

/-- Each point write materializes at most one root-to-leaf path. -/
theorem stored_cells_write_le (tree : Tree R depth) (address : Address depth) (entry : R) :
    storedCells (write tree address entry) ≤ storedCells tree + (depth + 1) := by
  induction depth with
  | zero => cases tree <;> simp [write, writeWithCount, storedCells]
  | succ depth ih =>
      have hChild := ih (child tree (address 0)) (Fin.tail address)
      cases tree with
      | vacant =>
          cases hb : address 0 <;>
            simp [write, writeWithCount, storedCells, branch, child, hb] at hChild ⊢ <;>
            omega
      | node cache left right =>
          cases hb : address 0 <;>
            simp [write, writeWithCount, storedCells, branch, child, hb] at hChild ⊢ <;>
            omega

/-- Recompute listed leaves and count all cell writes, including repeated addresses. -/
def refreshWithCount (tree : Tree R depth) (addresses : List (Address depth))
    (entries : Address depth → R) : Tree R depth × ℕ :=
  match addresses with
  | [] => (tree, 0)
  | selected :: rest =>
      let first := writeWithCount tree selected (entries selected)
      let remaining := refreshWithCount first.1 rest entries
      (remaining.1, first.2 + remaining.2)

/-- Recompute only the listed leaves, using the same entry function at repeated addresses. -/
def refresh (tree : Tree R depth) (addresses : List (Address depth)) (entries : Address depth → R) :
    Tree R depth :=
  (refreshWithCount tree addresses entries).1

/-- A batch of overwrites writes one full path per listed address. -/
theorem refresh_cell_count (tree : Tree R depth) (addresses : List (Address depth))
    (entries : Address depth → R) :
    (refreshWithCount tree addresses entries).2 = addresses.length * (depth + 1) := by
  induction addresses generalizing tree with
  | nil => simp [refreshWithCount]
  | cons _ _ ih =>
      simp only [refreshWithCount, write_cell_count, ih, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Refreshing any list of leaves preserves all caches. -/
theorem valid_refresh (tree : Tree R depth) (h : Valid tree) (addresses : List (Address depth))
    (entries : Address depth → R) : Valid (refresh tree addresses entries) := by
  induction addresses generalizing tree with
  | nil => exact h
  | cons address addresses ih =>
      exact ih _ (valid_write tree address (entries address) h)

/-- Refresh takes new entries on the supplied addresses and preserves every other entry. -/
theorem read_refresh (tree : Tree R depth) (addresses : List (Address depth))
    (entries : Address depth → R) (address : Address depth) :
    read (refresh tree addresses entries) address =
      if address ∈ addresses then entries address else read tree address := by
  induction addresses generalizing tree with
  | nil => simp [refresh, refreshWithCount]
  | cons selected addresses ih =>
      change read (refresh (write tree selected (entries selected)) addresses entries) address = _
      rw [ih, read_write]
      by_cases hTail : address ∈ addresses <;> by_cases hHead : address = selected <;>
        simp [List.mem_cons, hTail, hHead]

/-- Concatenate a prefix address and a local suffix address. -/
def joinAddress {remaining : ℕ} : (levels : ℕ) → Address levels → Address remaining →
    Address (remaining + levels)
  | 0, _, suffix => suffix
  | levels + 1, leading, suffix =>
      Fin.cons (leading 0) (joinAddress levels (Fin.tail leading) suffix)

/-- A split address has a computable equivalence with the flattened tree address. -/
def joinAddressEquiv {remaining : ℕ} : (levels : ℕ) →
    Address levels × Address remaining ≃ Address (remaining + levels)
  | 0 =>
    { toFun := Prod.snd
      invFun := fun suffix => (Fin.elim0, suffix)
      left_inv := fun _ => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl }
  | levels + 1 =>
    ((Fin.consEquiv (fun _ : Fin (levels + 1) => Bool)).symm.prodCongr (Equiv.refl (Address remaining))).trans
      ((Equiv.prodAssoc Bool (Address levels) (Address remaining)).trans
        (((Equiv.refl Bool).prodCongr (joinAddressEquiv levels)).trans
          (Fin.consEquiv (fun _ : Fin (remaining + levels + 1) => Bool))))

/-- The forward direction of the equivalence uses the tree's root-first concatenation. -/
theorem join_address_equiv_apply {remaining : ℕ} (levels : ℕ)
    (leading : Address levels) (suffix : Address remaining) :
    joinAddressEquiv levels (leading, suffix) = joinAddress levels leading suffix := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
    exact congrArg (Fin.cons (n := remaining + levels) (α := fun _ => Bool) (leading 0))
      (ih (Fin.tail leading))

/-- Select a subtree by its prefix address. -/
def subtree {remaining : ℕ} : (levels : ℕ) → Tree R (remaining + levels) →
    Address levels → Tree R remaining
  | 0, tree, _ => tree
  | levels + 1, tree, leading => subtree levels (child tree (leading 0)) (Fin.tail leading)

/-- Subtrees inherit the cache invariant. -/
theorem valid_subtree {remaining : ℕ} (levels : ℕ) (tree : Tree R (remaining + levels))
    (leading : Address levels) (h : Valid tree) : Valid (subtree levels tree leading) := by
  induction levels with
  | zero => exact h
  | succ levels ih => exact ih _ _ (valid_child tree (leading 0) h)

/-- A fixed level partitions the total cached mass into its subtree masses. -/
theorem mass_eq_sum_subtrees {remaining : ℕ} (levels : ℕ) (tree : Tree R (remaining + levels))
    (h : Valid tree) : mass tree = ∑ address : Address levels, mass (subtree levels tree address) := by
  induction levels with
  | zero =>
      let _ : Unique (Address 0) := ⟨⟨Fin.elim0⟩, fun _ => Subsingleton.elim _ _⟩
      simp [subtree]
  | succ levels ih =>
      rw [mass_eq_children tree h, ih _ (valid_child tree false h), ih _ (valid_child tree true h)]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (levels + 1) => Bool))
        (fun pair => mass (subtree (levels + 1) tree (Fin.cons pair.1 pair.2)))
        (fun address => mass (subtree (levels + 1) tree address)) (fun _ => rfl)]
      simp [Fintype.sum_prod_type, subtree, add_comm]

/-- A subtree read agrees with the corresponding full address. -/
theorem read_subtree {remaining : ℕ} (levels : ℕ) (tree : Tree R (remaining + levels))
    (leading : Address levels) (suffix : Address remaining) :
    read (subtree levels tree leading) suffix = read tree (joinAddress levels leading suffix) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simpa [subtree, joinAddress, read] using ih (child tree (leading 0)) (Fin.tail leading)

/-- A full address determines both its prefix and its suffix. -/
theorem join_address_eq_iff {remaining : ℕ} (levels : ℕ)
    (leading otherPrefix : Address levels) (suffix otherSuffix : Address remaining) :
    joinAddress levels leading suffix = joinAddress levels otherPrefix otherSuffix ↔
      leading = otherPrefix ∧ suffix = otherSuffix := by
  induction levels with
  | zero => simp [joinAddress, Subsingleton.elim leading otherPrefix]
  | succ levels ih =>
      constructor
      · intro h
        have hHead := congrFun h 0
        have hTail := congrArg Fin.tail h
        simp only [joinAddress, Fin.cons_zero] at hHead
        simp only [joinAddress, Fin.tail_cons] at hTail
        rcases (ih _ _).1 hTail with ⟨hPrefix, hSuffix⟩
        exact ⟨by rw [← Fin.cons_self_tail leading, ← Fin.cons_self_tail otherPrefix, hHead, hPrefix],
          hSuffix⟩
      · rintro ⟨rfl, rfl⟩
        rfl

end Qatlib.Foundations.QramData.SquaredNormTree
