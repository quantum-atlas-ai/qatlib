/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.ComputedGrid.ComputedDysonGridProgram

/-!
# Computed Dyson accuracy contract

This module defines `Lemma5DysonComputedParameters`, combining structural properties of the
computed grid with a dyadic approximation bound. Its hypotheses express bounded Hermitian
evolution, a continuous derivative, and an integral mean derivative bound, following the setting
of [LowWiebe2018].

## Main statements

* `Lemma5DysonComputedParameters`: the accuracy and exact counting specification for computed
  runs.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.ComputedGrid
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that every computed Dyson run satisfies the grid and counting identities and
error at most `2⁻ᵏ` under the stated bounded-field and mean derivative hypotheses. -/
def Lemma5DysonComputedParameters : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ)
    (t Λ χ : ℝ) (k : ℕ),
    Continuous H → Continuous Hd →
    (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    0 ≤ t → 0 ≤ Λ → 0 ≤ χ →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Λ * t ≤ Real.log 2 →
    (∫ u in (0 : ℝ)..t, ‖Hd u‖) ≤ χ * t →
    let r := computedDysonGridRun H t Λ χ k
    1 ≤ r.gridSize ∧ r.cutoff ^ 2 ≤ r.gridSize ∧ r.sampleReads = r.gridSize ∧
    r.matrixMultiplications = (∑ l ∈ Finset.range (r.cutoff + 1),
      l * Nat.choose r.gridSize l) ∧
    ‖r.approximation - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ (1 / 2 : ℝ) ^ k

end Qatlib.Concepts.InteractionEvo.ComputedGrid
