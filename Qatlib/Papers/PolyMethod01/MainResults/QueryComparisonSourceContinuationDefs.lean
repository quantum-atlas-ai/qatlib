/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryComparisonSource
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonContinuation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.BooleanQueryMinimumBounds
import Mathlib.Tactic.Linarith

/-!
# Deterministic search classes and scan trees

The abbreviation `SearchTree` uses optional output indices to express search, and the
correctness predicates distinguish absence of any true coordinate from finding a true
coordinate. The module defines the visited-address set, finite classes of search trees, their
minimum correct depths, and the sequential scan construction. These results accompany the
polynomial-method analysis in [BealsEtAl2001].

## Main statements

* `SearchTreeCorrect`: The condition that the tree returns `none` exactly on all-false inputs
  and returns a true coordinate whenever a true coordinate exists.
* `ZeroErrorSearchClass.minDepth`: The least depth in a nonempty correct-tree depth set.
* `searchScanTree`: The search tree that scans a list in order and halts at the first true
  coordinate, returning `none` if none is found.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PolyMethod01.MainResults

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- A Boolean query tree whose output is either an input coordinate or `none`. -/
abbrev SearchTree (I : Type) := BoolQueryTree I (Option I)

/-- The condition that the tree returns `none` exactly on all-false inputs and returns a true
coordinate whenever a true coordinate exists. -/
def SearchTreeCorrect {I : Type} (t : SearchTree I) (g : I → Bool) : Prop :=
  ((BoolQueryTree.Run g t).1 = none ↔ ∀ i : I, g i = false) ∧
    (∀ i : I, g i = true → ∃ j, (BoolQueryTree.Run g t).1 = some j ∧ g j = true)

/-- The condition that the tree returns `none` exactly when all listed coordinates are false and
returns a true coordinate whenever a listed true coordinate exists. -/
def SearchTreeCorrectOn {I : Type} (l : List I) (t : SearchTree I) (g : I → Bool) : Prop :=
  ((BoolQueryTree.Run g t).1 = none ↔ ∀ i ∈ l, g i = false) ∧
    (∀ i ∈ l, g i = true → ∃ j, (BoolQueryTree.Run g t).1 = some j ∧ g j = true)

/-- The finite set of distinct coordinates queried along the execution on a given Boolean input. -/
def queriedSet {I : Type} [DecidableEq I] {Output : Type} :
    BoolQueryTree I Output → (I → Bool) → Finset I
  | .halt _, _ => ∅
  | .ask i onFalse onTrue, g =>
      insert i (if g i then queriedSet onTrue g else queriedSet onFalse g)

/-- A nonempty finite list of search trees forming the allowed search class. -/
structure ZeroErrorSearchClass (I : Type) where
  trees : List (SearchTree I)
  nonempty : trees ≠ []

/-- The finite set of maximum query counts of trees in the class that are correct on every
input. -/
def ZeroErrorSearchClass.depthSet (M : ZeroErrorSearchClass I) : Finset ℕ :=
  (M.trees.filter (fun t => decide (∀ g : I → Bool, SearchTreeCorrect t g))).map
    BoolQueryTree.MaxQueries |>.toFinset

/-- The least depth in a nonempty correct-tree depth set. -/
noncomputable def ZeroErrorSearchClass.minDepth (M : ZeroErrorSearchClass I)
    (h : ∃ n, n ∈ M.depthSet) : ℕ :=
  finsetMinNat M.depthSet h

/-- The search tree that scans a list in order and halts at the first true coordinate, returning
`none` if none is found. -/
def searchScanTree : List I → SearchTree I
  | [] => .halt none
  | i :: l => .ask i (searchScanTree l) (.halt (some i))

/-- The Boolean predicate that all input coordinates are false. -/
def andFunction (g : I → Bool) : Bool := decide (∀ i, g i = false)

/-- The search class consisting of the single sequential scan tree for `l`. -/
def scanSearchClass (l : List I) : ZeroErrorSearchClass I where
  trees := [searchScanTree l]
  nonempty := by simp

end Qatlib.Papers.PolyMethod01.MainResults
