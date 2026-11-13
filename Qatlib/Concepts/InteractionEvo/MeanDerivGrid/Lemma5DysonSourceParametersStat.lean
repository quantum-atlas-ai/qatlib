/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationStat

/-!
# Dyson grid source-parameter statement

`Lemma5DysonSourceParameters` specifies a sufficient grid-size and truncation-order condition
for approximating a finite-dimensional ordered evolution. It uses a continuous derivative field
and a bound on the Hermitian Hamiltonian over the interval. These estimates support the
interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `Lemma5DysonSourceParameters`: the proposition asserting total operator-norm error at most ε.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that a short-time Hermitian evolution has Dyson grid error at most ε when
the explicit derivative-integral grid-size condition and factorial tail bound hold. -/
def Lemma5DysonSourceParameters : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (K M : ℕ),
    Continuous H → Continuous Hd →
    (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    0 < t → 0 < M → 0 < ε →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Λ * t ≤ Real.log 2 →
    (16 : ℝ) * t ^ 2 * ((1 / t) * ∫ u in (0 : ℝ)..t, ‖Hd u‖ + Λ ^ 2) / ε ≤ M →
    (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε / 2 →
    ‖truncatedDysonGridSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ ε

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
