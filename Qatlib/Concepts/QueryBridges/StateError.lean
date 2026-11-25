/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

@[expose] public section

/-!
# State-distance and readout bridges

This module exposes the pure-state Euclidean-to-readout bridge under a query-toolkit namespace.
For normalized states, every finite measurement event changes by at most twice the Euclidean state
distance.  The event form is the finite-outcome total-variation/success-probability interface used
by ordinary algorithm consumers.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout

namespace Qatlib.Concepts.QueryBridges

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The success-probability perturbation of a finite event is bounded by twice the Euclidean
distance between normalized pure states. -/
theorem success_probability_perturbation (ψ φ : QState I) (S : Finset I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    |MeasureProb ψ S - MeasureProb φ S| ≤
      2 * ‖toEuclidean_fromVec (ψ - φ)‖ :=
  measureProb_sub_le_two_mul_l2 ψ φ S hψ hφ

/-- A common unitary readout preserves the same success-probability perturbation bound. -/
theorem success_probability_after_unitary (U : Matrix I I ℂ) (ψ φ : QState I) (S : Finset I)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hψ : Normalized ψ) (hφ : Normalized φ) :
    |MeasureProb (ApplyGate U ψ) S - MeasureProb (ApplyGate U φ) S| ≤
      2 * ‖toEuclidean_fromVec (ψ - φ)‖ :=
  measureProb_applyGate_sub_le_two_mul_l2 U ψ φ S hU hψ hφ

end Qatlib.Concepts.QueryBridges
