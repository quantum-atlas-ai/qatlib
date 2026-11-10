/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFind
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
namespace GeneralElementDistinctnessDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

structure compactEntry where

  index : ℕ

  value : ℕ
  deriving DecidableEq, Repr

abbrev compactEntries := Finset compactEntry

def compactEntrySlot (e : compactEntry) : ℕ := e.index

def compactEntryValue (e : compactEntry) : ℕ := e.value

def nearPrimePower (p a q : ℕ) : Prop := Nat.Prime p ∧ 0 < a ∧ q = p ^ (2 * a)

def primeInSqrtInterval (k N p : ℕ) : Prop :=
  Real.sqrt (N : ℝ) ≤ p ∧ (p : ℝ) ≤ Real.sqrt ((1 + 1 / (2 * (k : ℝ) ^ 2)) * N)

end GeneralElementDistinctnessDefs
end Qatlib.Concepts.WalkFind.SearchAlgorithm
