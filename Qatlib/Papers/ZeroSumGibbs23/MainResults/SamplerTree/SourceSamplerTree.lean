/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGibbs23 — Lemma 1 (Sampler tree)

Fixed arXiv:2301.03763v1, Lemma 1, printed p.8 (Section 3.2).

> Let `η ∈ ℝ≥0` and `m ∈ ℕ`. There is a classical data structure, `SamplerTree`,
> supporting a tree on `O(m)` nodes such that `[m]` corresponds to leaves, with
> the operations `Init(m, η_fixed)`, `Update(i) : x_i ← x_i + η` and
> `SubtreeSum(v) : ∑_{i ∈ subtree(v)} x_i`. The total runtime of `T` calls to
> `Update` is `O(T log m)`, and calls to `SubtreeSum` cost `O(1)`.

We model the interface exactly: an index type of nodes, a leaf map
`[m] → Node`, a leaf set for every node, and a stored-value function computing
subtree sums. The witness realizing the printed bounds is the two-level tree
with one root and one leaf per coordinate (`m + 1` nodes): `SubtreeSum` reads a
single stored value and `Update(i)` rewrites only the leaf `i` and the root.
This is the standard "subtree sums propagated on update" implementation
specialised to depth two; the paper's binary tree realizes the same interface
with depth `O(log m)`, and that additional structure is used only in Lemma 7
(loading the tree into a quantum oracle), which is formalized separately in
`MainResults/OracleLoading`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.SamplerTree

open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model

variable {m : ℕ}

/-! ### The two-level sampler tree -/

/-- Nodes of the sampler tree: one root together with one leaf per coordinate
of `x ∈ ℝ^m`. -/
abbrev STNode (m : ℕ) := Unit ⊕ Fin m

/-- The root node. -/
def stRoot (m : ℕ) : STNode m := Sum.inl ()

/-- The leaf carrying coordinate `i`. -/
def stLeaf {m : ℕ} (i : Fin m) : STNode m := Sum.inr i

/-- The set of coordinates contained in the subtree rooted at a node. -/
def stLeaves (m : ℕ) : STNode m → Finset (Fin m)
  | Sum.inl _ => Finset.univ
  | Sum.inr i => {i}

/-- The number of node rewrites performed by a single `Update`: the leaf and the
root. -/
def stUpdateWrites : ℕ := 2

/-- Reads performed by a single `SubtreeSum`: the stored value is returned
directly. -/
def stSubtreeReads : ℕ := 1

/-- `Init(m, η_fixed)`: the dynamic vector starts at `x = 0^m`. -/
def stInit (m : ℕ) : Fin m → ℝ := fun _ => 0

/-- `Update(i)`: `x_i ← x_i + η`. -/
def stUpdate {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (η : ℝ) : Fin m → ℝ :=
  Function.update x i (x i + η)

/-- The stored subtree sums of a vector `x`: leaves store `x_i`, the root stores
the total mass. -/
def stSum {m : ℕ} (x : Fin m → ℝ) : STNode m → ℝ
  | Sum.inl _ => ∑ i, x i
  | Sum.inr i => x i

/-- The root stores the total mass `Σ_i x_i`. -/
theorem stSum_root (x : Fin m → ℝ) : stSum x (stRoot m) = ∑ i, x i := rfl

/-- The leaf `i` stores `x_i`. -/
theorem stSum_leaf (x : Fin m → ℝ) (i : Fin m) : stSum x (stLeaf i) = x i := rfl

/-- `SubtreeSum(v)` returns the sum of `x_i` over the subtree of `v`. -/
theorem stSum_eq_sum_leaves (x : Fin m → ℝ) (v : STNode m) :
    stSum x v = ∑ i ∈ stLeaves m v, x i := by
  cases v with
  | inl _ => simp [stSum, stLeaves]
  | inr i => simp [stSum, stLeaves]

/-- After `Init`, every subtree sum is zero. -/
theorem stSum_init (v : STNode m) : stSum (stInit m) v = 0 := by
  cases v with
  | inl _ => simp [stSum, stInit]
  | inr i => simp [stSum, stInit]

/-- The leaf storage after `Update(i)` increases by exactly `η` at `i`. -/
theorem stSum_leaf_update (x : Fin m → ℝ) (i j : Fin m) (η : ℝ) :
    stSum (stUpdate x i η) (stLeaf j) = stSum x (stLeaf j) + (if j = i then η else 0) := by
  simp only [stSum, stLeaf, stUpdate]
  rw [Function.update_apply]
  by_cases h : j = i <;> simp [h]

/-- In particular the updated leaf itself grows by `η`. -/
theorem stSum_leaf_update_self (x : Fin m → ℝ) (i : Fin m) (η : ℝ) :
    stSum (stUpdate x i η) (stLeaf i) = stSum x (stLeaf i) + η := by
  simp [stSum_leaf_update]

/-- The root storage after `Update(i)` increases by exactly `η`. -/
theorem stSum_root_update (x : Fin m → ℝ) (i : Fin m) (η : ℝ) :
    stSum (stUpdate x i η) (stRoot m) = stSum x (stRoot m) + η := by
  simp only [stSum, stRoot, stUpdate]
  have h : ∀ j, Function.update x i (x i + η) j = x j + (if j = i then η else 0) := by
    intro j
    rw [Function.update_apply]
    by_cases h : j = i <;> simp [h]
  simp only [h, Finset.sum_add_distrib]
  have hite : (∑ j : Fin m, if j = i then η else 0) = η := by simp
  rw [hite]

/-- Only the two nodes on the path of `i` (the leaf and the root) change their
stored sums under `Update(i)`. -/
theorem stSum_update_eq_of_ne (x : Fin m → ℝ) (i : Fin m) (η : ℝ) (v : STNode m)
    (hv1 : v ≠ stLeaf i) (hv2 : v ≠ stRoot m) :
    stSum (stUpdate x i η) v = stSum x v := by
  cases v with
  | inl u =>
    exact absurd rfl hv2
  | inr j =>
    have hji : j ≠ i := fun h => hv1 (by simp [h, stLeaf])
    simp only [stSum, stUpdate]
    rw [Function.update_apply]
    simp [hji]

/-- The node count of the two-level tree is `m + 1 ≤ 2m + 1`. -/
theorem stNode_card (m : ℕ) : Fintype.card (STNode m) ≤ 2 * m + 1 := by
  have h : Fintype.card (STNode m) = 1 + m := by
    simp [STNode, Fintype.card_sum, Fintype.card_fin]
  linarith

/-- `T` calls to `Update` perform at most `2T` node rewrites, which is
`O(T log m)`; a `SubtreeSum` costs one stored lookup. -/
theorem stRuntime (m : ℕ) :
    stUpdateWrites ≤ 2 ∧ stSubtreeReads = 1 ∧
      ∀ T : ℕ, T * stUpdateWrites ≤ T * (Nat.clog 2 (m + 1) + 2) := by
  refine ⟨le_refl 2, rfl, fun T => ?_⟩
  have hle : stUpdateWrites ≤ Nat.clog 2 (m + 1) + 2 := by
    simp [stUpdateWrites]
  exact Nat.mul_le_mul_left T hle

/-- **Lemma 1 (Sampler tree)**, printed p.8. There is a classical data structure
on `O(m)` nodes with `[m]` as leaves supporting `Init`, `Update(i) : x_i ← x_i + η`
and `SubtreeSum`, where `SubtreeSum` costs one lookup and a single `Update` only
rewrites the two nodes on the leaf-to-root path; consequently `T` updates cost at
most `2T ≤ T (log₂(m+1) + 2)` node rewrites. -/
theorem lemma1_sampler_tree (m : ℕ) :
    ∃ (Node : Type) (_ : Fintype Node) (_ : DecidableEq Node)
      (leafOf : Fin m → Node) (subtreeLeaves : Node → Finset (Fin m))
      (root : Node) (subtreeSum : (Fin m → ℝ) → Node → ℝ)
      (update : (Fin m → ℝ) → Fin m → ℝ → Fin m → ℝ),
      Fintype.card Node ≤ 2 * m + 1 ∧
      (∀ i, subtreeLeaves (leafOf i) = {i}) ∧
      subtreeLeaves root = Finset.univ ∧
      (∀ (x : Fin m → ℝ) (v : Node), subtreeSum x v = ∑ i ∈ subtreeLeaves v, x i) ∧
      (∀ (x : Fin m → ℝ) (i : Fin m) (η : ℝ),
        subtreeSum (update x i η) (leafOf i) = subtreeSum x (leafOf i) + η ∧
        subtreeSum (update x i η) root = subtreeSum x root + η) ∧
      (∀ (x : Fin m → ℝ) (i : Fin m) (η : ℝ) (v : Node),
        v ≠ leafOf i → v ≠ root → subtreeSum (update x i η) v = subtreeSum x v) ∧
      (∀ T : ℕ, T * stUpdateWrites ≤ T * (Nat.clog 2 (m + 1) + 2)) ∧
      stSubtreeReads = 1 := by
  refine ⟨STNode m, inferInstance, inferInstance, stLeaf, stLeaves m, stRoot m, stSum,
    stUpdate, stNode_card m, ?_, ?_, ?_, ?_, ?_, (stRuntime m).2.2, (stRuntime m).2.1⟩
  · intro i
    simp [stLeaf, stLeaves]
  · simp [stRoot, stLeaves]
  · intro x v
    exact stSum_eq_sum_leaves x v
  · intro x i η
    exact ⟨stSum_leaf_update_self x i η, stSum_root_update x i η⟩
  · intro x i η v hv1 hv2
    exact stSum_update_eq_of_ne x i η v hv1 hv2

end Qatlib.Papers.ZeroSumGibbs23.MainResults.SamplerTree
