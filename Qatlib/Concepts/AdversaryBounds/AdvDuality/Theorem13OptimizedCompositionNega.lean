/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem13OptimizedCompositionStat

/-!
# Optimized adversary composition lower bound

`theorem13OptimizedComposition` proves the proposition `Theorem13OptimizedComposition` by
applying the optimized adversary composition theorem. The outer coordinate costs may be any real
values whose nonnegative extended-real images are bounded by the corresponding inner adversary
values.

For nonconstant inner functions with positive input lengths and nonnegative coordinate costs,
the composed adversary value bounds the outer weighted adversary value from below. This is the
formal composition statement associated with Theorem 13 of [HoyerLeeSpalek2007].

## Main statements

* `theorem13OptimizedComposition`: establishes the optimized weighted adversary composition
  inequality.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- For nonconstant inner functions with positive input lengths and nonnegative coordinate
costs, the composed optimized adversary bound is at least the outer bound whenever each
outer cost is bounded by the corresponding inner bound. See [Hoyer, Lee, and Spalek, Theorem
13][HoyerLeeSpalek2007]. -/
theorem theorem13OptimizedComposition : Theorem13OptimizedComposition := by
  intro k X _ _ n hne g hnc f gin α hα β hβ
  exact advPlus_composition_ge k X n hne g hnc f gin α hα β hβ
end Qatlib.Concepts.AdversaryBounds.AdvDuality
