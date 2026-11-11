/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Hermitian evolution perturbation statement

This module defines `HermitianEvolutionLipschitz`, the operator norm perturbation estimate for
finite Hermitian Hamiltonians at arbitrary real times. The mathematical background is developed
in [GilyenSuLowWiebe2019].

## Main statements

* `HermitianEvolutionLipschitz`: the assertion that evolution is Lipschitz in the Hamiltonian
  with constant `|t|`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The assertion that the distance between two Hermitian time evolutions is at most `|t|` times
the distance between their Hamiltonians. -/
def HermitianEvolutionLipschitz : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H H' : Matrix I I ℂ),
    H.IsHermitian → H'.IsHermitian → ∀ t : ℝ,
      ‖Qatlib.Foundations.PureStateMath.HamiltonianEvolution H t -
        Qatlib.Foundations.PureStateMath.HamiltonianEvolution H' t‖ ≤ |t| * ‖H - H'‖

end Qatlib.Concepts.QsvtCore.HamiltonianSim
