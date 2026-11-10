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

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SortDistinct01.MainResults.PebbleTrees

inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree
deriving DecidableEq, Repr

namespace BinTree

def numLeaves : BinTree → ℕ
  | .leaf => 1
  | .node l r => l.numLeaves + r.numLeaves

def height : BinTree → ℕ
  | .leaf => 0
  | .node l r => 1 + max l.height r.height

def subtreeAt (t : BinTree) : List Bool → Option BinTree
  | [] => some t
  | b :: rest =>
    match t with
    | .leaf => none
    | .node l r => (if b then r else l).subtreeAt rest

def isLeafAt (t : BinTree) (p : List Bool) : Prop := t.subtreeAt p = some .leaf

def internalVertices : BinTree → Finset (List Bool)
  | .leaf => ∅
  | .node l r =>
      insert [] (l.internalVertices.image (fun p => false :: p) ∪
        r.internalVertices.image (fun p => true :: p))

end BinTree

def prefixes (p : List Bool) : Finset (List Bool) :=
  (Finset.range (p.length + 1)).image (fun n => p.take n)

def properAncestor (q p : List Bool) : Prop := q ∈ prefixes p ∧ q ≠ p

instance decidableProperAncestor (p : List Bool) : DecidablePred (fun q => properAncestor q p) :=
  fun q => by
    unfold properAncestor
    infer_instance

structure PebbleCovering (T : BinTree) (k : ℕ) where

  peb : Fin k → List Bool → ℕ

  interior_only : ∀ c v, v ∉ T.internalVertices → peb c v = 0

  path_one : ∀ c (ℓ : List Bool), T.isLeafAt ℓ →
    ∑ v ∈ T.internalVertices.filter (fun v => v ∈ prefixes ℓ), peb c v = 1

  dominates : ∀ c v, v ∈ T.internalVertices →
    (∑ q ∈ T.internalVertices.filter (fun q => properAncestor q v), peb c q) ≤ peb c v

namespace PebbleCovering

variable {T : BinTree} {k : ℕ}

def total (C : PebbleCovering T k) (c : Fin k) : ℕ :=
  ∑ v ∈ T.internalVertices, C.peb c v

def ancestorSum (C : PebbleCovering T k) (c : Fin k) (v : List Bool) : ℕ :=
  ∑ q ∈ T.internalVertices.filter (fun q => properAncestor q v), C.peb c q

def IsFair (C : PebbleCovering T k) : Prop :=
  ∀ c c' : Fin k, C.total c = C.total c'

def IsTight (C : PebbleCovering T k) : Prop :=
  ∀ c v, v ∈ T.internalVertices →
    C.peb c v = C.ancestorSum c v ∨ C.ancestorSum c v = 0

end PebbleCovering

theorem lemma11_params_two :
    (2 : ℕ) / 3 + Nat.log2 2 = 1 ∧ Nat.log 4 (2 / 2) = 0 := by
  refine ⟨by decide, by decide⟩

theorem lemma11_params_four :
    (4 : ℕ) / 3 + Nat.log2 4 = 3 ∧ Nat.log 4 (4 / 2) = 0 := by
  refine ⟨by decide, by decide⟩

theorem PebbleCovering.total_le_self {T : BinTree} {k N' : ℕ}
    (C : PebbleCovering T k) (h : ∀ c : Fin k, C.total c ≤ N') :
    ∀ c : Fin k, C.total c ≤ N' := h

end Qatlib.Papers.SortDistinct01.MainResults.PebbleTrees
