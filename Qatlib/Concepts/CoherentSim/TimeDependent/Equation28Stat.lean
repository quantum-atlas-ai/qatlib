/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Defs

/-!
# Error bound for a time dependent simulation segment

`Equation28` states an operator norm error bound for the grid approximation `equation28Segment`
to ordered evolution. The bound separates the truncation term of order `K + 1` from the grid
error controlled by the Hamiltonian norm bound and its Lipschitz constant.

The mathematical context is discussed in [BerryEtAl2015Taylor].

## Main statements

* `Equation28`: The segment error bound for a continuous Hermitian Hamiltonian with bounded norm
  and Lipschitz variation.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.CoherentSim.TimeDependent

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The statement that a grid segment approximates ordered evolution with error at most exp(Λτ)
times the sum of (Λτ)^(K + 1)/(K + 1)! and (Λ² + L)τ²/(2M), under the stated continuity,
Hermiticity, norm and Lipschitz bounds. -/
def Equation28 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ) (τ Λ L : ℝ) (M K : ℕ),
    Continuous H → 0 ≤ τ → 0 ≤ Λ → 0 ≤ L → 0 < M →
    (∀ u ∈ Set.Icc 0 τ, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    (∀ u ∈ Set.Icc 0 τ, ∀ v ∈ Set.Icc 0 τ, ‖H u - H v‖ ≤ L * |u - v|) →
    ‖equation28Segment H τ M K - orderedEvolution (fun u => Complex.I • H u) 0 τ‖ ≤
      Real.exp (Λ * τ) *
        ((Λ * τ) ^ (K + 1) / (((K + 1).factorial : ℕ) : ℝ) + (Λ ^ 2 + L) * τ ^ 2 / (2 * M))

end Qatlib.Concepts.CoherentSim.TimeDependent
