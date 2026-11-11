/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalDefs
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Coherent acceptance-coin specification

This module states the coherent acceptance-coin specification motivated by Eqs. (2)-(3) of
[TemmeEtAl2011]. For every normalized proposal amplitude vector, it requires unitarity, the
exact state after the controlled coin operation, and the Born mass of the accepting outcomes.

## Main statements

* `CoherentInstrumentSubgoal` packages the controlled-gate, amplitude, and acceptance-mass
  conclusions for all finite energy tables.

## References

* [Temme et al., 2011][TemmeEtAl2011], *Quantum Metropolis Sampling*, Eqs. (2)-(3).
-/

set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin

open Matrix

/-- The proposition requiring unitarity, the exact accepting and rejecting output amplitudes,
and the proposal-weighted acceptance probability for every normalized proposal vector. It
specifies the coherent coin step of Eqs. (2)-(3) in [TemmeEtAl2011]. -/
def CoherentInstrumentSubgoal : Prop :=
  ∀ (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (x : Fin D → ℂ),
    (∑ k, ‖x k‖ ^ 2 = 1) →
    (metropolisControlledCoin E β ∈ Matrix.unitaryGroup _ ℂ) ∧
    (ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x)
        = fun p : Fin D × Fin D × Fin D × Fin 2 =>
          if p.2.1 = i ∧ p.1 = p.2.2.1 then
            if p.2.2.2 = 1 then
              x p.1 * ((Real.sqrt (thermalAcceptance E β i p.1) : ℝ) : ℂ)
            else
              x p.1 * ((Real.sqrt (1 - thermalAcceptance E β i p.1) : ℝ) : ℂ)
          else 0) ∧
    (MeasureProb (ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x))
        (Finset.filter (fun p : Fin D × Fin D × Fin D × Fin 2 => p.2.2.2 = 1) Finset.univ)
      = ∑ k, ‖x k‖ ^ 2 * thermalAcceptance E β i k)

end Qatlib.Papers.QMetropolis11.AcceptanceCoin
