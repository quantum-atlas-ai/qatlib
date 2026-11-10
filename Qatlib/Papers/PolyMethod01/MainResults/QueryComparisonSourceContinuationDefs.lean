/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryComparisonSource
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonContinuation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.BooleanQueryMinimumBounds
import Mathlib.Tactic.Linarith
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

abbrev SearchTree (I : Type) := BoolQueryTree I (Option I)

def SearchTreeCorrect {I : Type} (t : SearchTree I) (g : I → Bool) : Prop :=
  ((BoolQueryTree.Run g t).1 = none ↔ ∀ i : I, g i = false) ∧
    (∀ i : I, g i = true → ∃ j, (BoolQueryTree.Run g t).1 = some j ∧ g j = true)

def SearchTreeCorrectOn {I : Type} (l : List I) (t : SearchTree I) (g : I → Bool) : Prop :=
  ((BoolQueryTree.Run g t).1 = none ↔ ∀ i ∈ l, g i = false) ∧
    (∀ i ∈ l, g i = true → ∃ j, (BoolQueryTree.Run g t).1 = some j ∧ g j = true)

def queriedSet {I : Type} [DecidableEq I] {Output : Type} :
    BoolQueryTree I Output → (I → Bool) → Finset I
  | .halt _, _ => ∅
  | .ask i onFalse onTrue, g =>
      insert i (if g i then queriedSet onTrue g else queriedSet onFalse g)

structure ZeroErrorSearchClass (I : Type) where
  trees : List (SearchTree I)
  nonempty : trees ≠ []

def ZeroErrorSearchClass.depthSet (M : ZeroErrorSearchClass I) : Finset ℕ :=
  (M.trees.filter (fun t => decide (∀ g : I → Bool, SearchTreeCorrect t g))).map
    BoolQueryTree.MaxQueries |>.toFinset

noncomputable def ZeroErrorSearchClass.minDepth (M : ZeroErrorSearchClass I)
    (h : ∃ n, n ∈ M.depthSet) : ℕ :=
  finsetMinNat M.depthSet h

def searchScanTree : List I → SearchTree I
  | [] => .halt none
  | i :: l => .ask i (searchScanTree l) (.halt (some i))

def andFunction (g : I → Bool) : Bool := decide (∀ i, g i = false)

def scanSearchClass (l : List I) : ZeroErrorSearchClass I where
  trees := [searchScanTree l]
  nonempty := by simp

end Qatlib.Papers.PolyMethod01.MainResults
