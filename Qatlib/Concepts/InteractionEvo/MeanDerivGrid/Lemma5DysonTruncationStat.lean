/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonAuxiliary

/-!
# Statement of the Dyson truncation error budget

`Lemma5DysonTruncation` packages the hypotheses for a truncated Dyson grid sum to approximate
ordered evolution within ε. Its discretization budget combines a quadratic Hamiltonian term with
the integral of the derivative norm, while its truncation budget is a factorial tail. These
estimates support the interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `Lemma5DysonTruncation`: the split-budget error proposition.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that a short-time, continuously differentiable Hermitian Hamiltonian has
total Dyson grid error at most ε when its discretization and factorial tail terms are each
at most ε/2. -/
def Lemma5DysonTruncation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (K M : ℕ),
    Continuous H → Continuous Hd →
    (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    0 < t → 0 < M → 0 < ε →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Λ * t ≤ Real.log 2 →
    Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * ∫ u in (0 : ℝ)..t, ‖Hd u‖ ≤ ε / 2 →
    (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε / 2 →
    ‖truncatedDysonGridSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ ε

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
