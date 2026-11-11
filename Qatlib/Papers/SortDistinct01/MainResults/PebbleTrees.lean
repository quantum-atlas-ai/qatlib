/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Binary trees and colored pebble coverings

This module defines finite binary trees, Boolean path addresses, and colored pebble coverings
with support, path-sum, and ancestor-dominance conditions. It introduces fairness and tightness,
checks the numerical parameters at two and four leaves, and records a direct consequence of a
per-color total bound, providing definitions and small-parameter calculations for the pebble
construction in [HoyerNeerbekShi2001].

## Main statements

* `PebbleCovering`: A colored pebble assignment supported on internal vertices, with one pebble
  of each color along every root-to-leaf path and each internal count dominating its same-color
  proper-ancestor sum.
* `IsFair`: The property that every color has the same total number of pebbles.
* `IsTight`: The property that each internal vertex's pebble count equals its proper-ancestor
  sum whenever that sum is nonzero, for every color.

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SortDistinct01.MainResults.PebbleTrees

/-- Finite full binary trees, built from a leaf or a node with two subtrees. -/
inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree
deriving DecidableEq, Repr

namespace BinTree

/-- The number of leaves of a finite binary tree. -/
def numLeaves : BinTree → ℕ
  | .leaf => 1
  | .node l r => l.numLeaves + r.numLeaves

/-- The height of a binary tree, with leaves at height zero. -/
def height : BinTree → ℕ
  | .leaf => 0
  | .node l r => 1 + max l.height r.height

/-- The subtree reached by a Boolean path, using `false` for left and `true` for right, or
`none` if the path descends past a leaf. -/
def subtreeAt (t : BinTree) : List Bool → Option BinTree
  | [] => some t
  | b :: rest =>
    match t with
    | .leaf => none
    | .node l r => (if b then r else l).subtreeAt rest

/-- The property that path `p` selects a leaf of `t`. -/
def isLeafAt (t : BinTree) (p : List Bool) : Prop := t.subtreeAt p = some .leaf

/-- The finite set of Boolean paths selecting internal vertices of a binary tree. -/
def internalVertices : BinTree → Finset (List Bool)
  | .leaf => ∅
  | .node l r =>
      insert [] (l.internalVertices.image (fun p => false :: p) ∪
        r.internalVertices.image (fun p => true :: p))

end BinTree

/-- The finite set of all prefixes of a Boolean path, including the empty path and the full
path. -/
def prefixes (p : List Bool) : Finset (List Bool) :=
  (Finset.range (p.length + 1)).image (fun n => p.take n)

/-- The property that `q` is a prefix of `p` distinct from `p`. -/
def properAncestor (q p : List Bool) : Prop := q ∈ prefixes p ∧ q ≠ p

instance decidableProperAncestor (p : List Bool) : DecidablePred (fun q => properAncestor q p) :=
  fun q => by
    unfold properAncestor
    infer_instance

/-- A colored pebble assignment supported on internal vertices, with one pebble of each color
along every root-to-leaf path and each internal count dominating its same-color
proper-ancestor sum. -/
structure PebbleCovering (T : BinTree) (k : ℕ) where

  peb : Fin k → List Bool → ℕ

  interior_only : ∀ c v, v ∉ T.internalVertices → peb c v = 0

  path_one : ∀ c (ℓ : List Bool), T.isLeafAt ℓ →
    ∑ v ∈ T.internalVertices.filter (fun v => v ∈ prefixes ℓ), peb c v = 1

  dominates : ∀ c v, v ∈ T.internalVertices →
    (∑ q ∈ T.internalVertices.filter (fun q => properAncestor q v), peb c q) ≤ peb c v

namespace PebbleCovering

variable {T : BinTree} {k : ℕ}

/-- The total number of pebbles of color `c` on internal vertices. -/
def total (C : PebbleCovering T k) (c : Fin k) : ℕ :=
  ∑ v ∈ T.internalVertices, C.peb c v

/-- The number of pebbles of color `c` on proper ancestors of `v`. -/
def ancestorSum (C : PebbleCovering T k) (c : Fin k) (v : List Bool) : ℕ :=
  ∑ q ∈ T.internalVertices.filter (fun q => properAncestor q v), C.peb c q

/-- The property that every color has the same total number of pebbles. -/
def IsFair (C : PebbleCovering T k) : Prop :=
  ∀ c c' : Fin k, C.total c = C.total c'

/-- The property that each internal vertex's pebble count equals its proper-ancestor sum
whenever that sum is nonzero, for every color. -/
def IsTight (C : PebbleCovering T k) : Prop :=
  ∀ c v, v ∈ T.internalVertices →
    C.peb c v = C.ancestorSum c v ∨ C.ancestorSum c v = 0

end PebbleCovering

/-- At two leaves, the expressions `N/3 + Nat.log2 N` and `Nat.log 4 (N/2)` evaluate to `1` and
`0`, respectively, checking parameters from [Hoyer et al., Lemma 11][HoyerNeerbekShi2001]. -/
theorem lemma11_params_two :
    (2 : ℕ) / 3 + Nat.log2 2 = 1 ∧ Nat.log 4 (2 / 2) = 0 := by
  refine ⟨by decide, by decide⟩

/-- At four leaves, the expressions `N/3 + Nat.log2 N` and `Nat.log 4 (N/2)` evaluate to `3` and
`0`, respectively, checking parameters from [Hoyer et al., Lemma 11][HoyerNeerbekShi2001]. -/
theorem lemma11_params_four :
    (4 : ℕ) / 3 + Nat.log2 4 = 3 ∧ Nat.log 4 (4 / 2) = 0 := by
  refine ⟨by decide, by decide⟩

/-- A supplied bound `N'` on the total pebble count of every color holds for every color. -/
theorem PebbleCovering.total_le_self {T : BinTree} {k N' : ℕ}
    (C : PebbleCovering T k) (h : ∀ c : Fin k, C.total c ≤ N') :
    ∀ c : Fin k, C.total c ≤ N' := h

end Qatlib.Papers.SortDistinct01.MainResults.PebbleTrees
