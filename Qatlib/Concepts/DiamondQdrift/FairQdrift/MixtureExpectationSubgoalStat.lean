/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixture
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.DiamondQdrift.FairQdrift

open Qatlib

def MixtureExpectationSubgoal : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D : ℕ)
    (d : FinDist J) (U : J → Matrix (Fin D) (Fin D) ℂ),
    (∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) →
    ∀ (ρ : Matrix (Fin D) (Fin D) ℂ), IsDensityOperator ρ →
    IsDensityOperator (ChannelMixture d U ρ)

end Qatlib.Concepts.DiamondQdrift.FairQdrift
