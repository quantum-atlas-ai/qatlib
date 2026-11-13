/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Degree-normalized adjacency kernel

This module defines `expanderStep`, the real kernel obtained by dividing the Boolean adjacency
indicator by the degree parameter. Symmetry and row normalization are established separately
under the graph hypotheses.

The kernel is used for regular-graph instances of Szegedy walk search [Szegedy2004].

## Main statements

* `expanderStep`: the degree-normalized adjacency kernel.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

/-- The degree-normalized adjacency kernel, equal to `1 / d` on adjacent pairs and zero
elsewhere. -/
noncomputable def expanderStep (n d : ℕ) (adj : Fin n → Fin n → Bool) :
    Fin n → Fin n → ℝ :=
  fun i j => if adj i j then ((d : ℝ)⁻¹) else 0
end Qatlib.Concepts.WalkSearch.Th4Expander
