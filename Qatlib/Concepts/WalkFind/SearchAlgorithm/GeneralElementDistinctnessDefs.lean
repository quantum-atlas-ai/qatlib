/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFind

/-!
# Compact entries and prime-power predicates

This module defines the finite collections of indexed entries used by the general
element-distinctness bookkeeping. `compactEntrySlot` and `compactEntryValue` expose the two
natural-number fields of `compactEntry`.

`nearPrimePower` specifies an even positive power of a prime, and `primeInSqrtInterval` gives
the square-root interval used to obtain a narrow prime-square bound. These definitions support
the element-distinctness setting of [Ambainis2007ElementDistinctness].

## Main statements

* `compactEntries`: finite collections of indexed values.
* `nearPrimePower`: the predicate `q = p^(2 * a)` with prime `p` and positive `a`.
* `primeInSqrtInterval`: the interval condition for the prime-square reduction.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
namespace GeneralElementDistinctnessDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- An entry consisting of a natural-number index and a natural-number value. -/
structure compactEntry where

  index : ℕ

  value : ℕ
  deriving DecidableEq, Repr

/-- A finite set of compact entries. -/
abbrev compactEntries := Finset compactEntry

/-- The index identifying the slot of a compact entry. -/
def compactEntrySlot (e : compactEntry) : ℕ := e.index

/-- The stored natural-number value of a compact entry. -/
def compactEntryValue (e : compactEntry) : ℕ := e.value

/-- The predicate asserting that `p` is prime, `a` is positive, and `q = p^(2 * a)`. -/
def nearPrimePower (p a q : ℕ) : Prop := Nat.Prime p ∧ 0 < a ∧ q = p ^ (2 * a)

/-- The predicate placing `p` between `sqrt N` and `sqrt ((1 + 1 / (2 * k^2)) * N)`. -/
def primeInSqrtInterval (k N p : ℕ) : Prop :=
  Real.sqrt (N : ℝ) ≤ p ∧ (p : ℝ) ≤ Real.sqrt ((1 + 1 / (2 * (k : ℝ) ^ 2)) * N)

end GeneralElementDistinctnessDefs
end Qatlib.Concepts.WalkFind.SearchAlgorithm
