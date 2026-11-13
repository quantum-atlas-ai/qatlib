/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixture
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Unitary mixture state preservation specification

This module states `MixtureExpectationSubgoal` for a finite distribution of unitary matrices.
The property asserts that `ChannelMixture` preserves density operators, as required for the
randomized simulation channel of [Campbell2019].

## Main statements

* `MixtureExpectationSubgoal`: density preservation by a finite unitary mixture.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.DiamondQdrift.FairQdrift

open Qatlib

/-- Every finite probability mixture of unitary conjugations sends each density operator to a
density operator [Campbell2019]. -/
def MixtureExpectationSubgoal : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D : ℕ)
    (d : FinDist J) (U : J → Matrix (Fin D) (Fin D) ℂ),
    (∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) →
    ∀ (ρ : Matrix (Fin D) (Fin D) ℂ), IsDensityOperator ρ →
    IsDensityOperator (ChannelMixture d U ρ)

end Qatlib.Concepts.DiamondQdrift.FairQdrift
