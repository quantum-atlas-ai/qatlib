/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.LinearSystem

/-!
# Restricted HHL resolution specification

`CostRestrictedSubgoal` states the inverse-square positivity and reciprocal-grid estimate used
in the restricted HHL development. It isolates arithmetic consequences of a grid size at least
`κ / ε` in the linear-system context of [HarrowHassidimLloyd2009].

## Main statements

* `CostRestrictedSubgoal`: the arithmetic resolution contract.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

/-- The proposition that `κ ≥ 1`, `ε > 0`, and `M ≥ κ / ε` imply `1 / κ² > 0` and `M⁻¹ ≤ ε / κ`. -/
def CostRestrictedSubgoal : Prop :=
  ∀ (κ ε : ℝ), 1 ≤ κ → 0 < ε →
    ∀ (M : ℕ), (M : ℝ) ≥ κ / ε →
      0 < 1 / κ ^ 2 ∧ (M : ℝ)⁻¹ ≤ ε / κ

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
