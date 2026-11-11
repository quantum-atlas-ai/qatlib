/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Uniform resource growth bounds

This module records input size and inverse precision in `GrowthFilter` and defines elementary
uniform upper and lower resource bounds. `uniformUpperBound` uses a fixed coefficient and degree
for every natural input size; `uniformLowerBound` requires pointwise domination. These notions
fit the complexity framework of [KitaevShenVyalyi2002].

## Main statements

* `uniformUpperBound`: a polynomial bound `R n ≤ C * (n + 1) ^ d` for every `n`.
* `uniformLowerBound`: a bound `f n ≤ R n` for every `n`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open Qatlib

set_option autoImplicit false

/-- A pair of natural-number parameters recording input size and inverse error tolerance. -/
structure GrowthFilter where

  inputSize : ℕ

  inverseEpsilon : ℕ

/-- Requires `R n ≤ C * (n + 1) ^ d` for every natural number `n`, with the coefficient and
degree fixed in advance. -/
def uniformUpperBound (R : ℕ → ℕ) (C : ℕ) (d : ℕ) : Prop :=
  ∀ n : ℕ, R n ≤ C * (n + 1) ^ d

/-- Requires `f n ≤ R n` for every natural number `n`. -/
def uniformLowerBound (R : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, f n ≤ R n

end Qatlib.Concepts.ResourceBounds.AsymBounds
