/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionDefs
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt

/-!
# Covariance identities for fermionic circuit steps

Well-formed matchgate circuits act on covariance matrices through `covarianceRun`. The
measurement-step identity combines this evolution with `measurementUpdate`, assuming the stated
covariance relation for indices away from the measured mode. These results formalize the
indicated identities from [Bravyi2005Fermionic].

## Main statements

* `flo_correlation_evolution`: identifies circuit multiplication with the covariance run.
* `classical_flo_step`: combines circuit evolution and the conditional measurement update.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

/-- For a circuit of well-formed matchgates, the covariance matrix after multiplication by the
circuit operator equals `covarianceRun` applied to the initial covariance matrix. -/
theorem flo_correlation_evolution {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (M : Fock n) :
    covarianceMatrix (matchGateCircuitOp gl * M) = covarianceRun gl (covarianceMatrix M) :=
  covarianceMatrix_matchGateCircuit gl h M

/-- Under the stated covariance hypothesis away from the measured mode, a circuit followed by a
measurement has covariance equal to the Born weight times the measurement update of the
covariance run. This is the conditional covariance-step identity used for fermionic
simulation in [Bravyi2005Fermionic]. -/
theorem classical_flo_step {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (M : Fock n)
    (k : Fin n) (b : Bool)
    (hAway : ∀ a c : Fin (2 * n), ¬ isModeMajorana k a → ¬ isModeMajorana k c →
      covarianceMatrix (measurementProjector k b * (matchGateCircuitOp gl * M)) a c
        = bornWeight (matchGateCircuitOp gl * M) k b *
            covarianceMatrix (matchGateCircuitOp gl * M) a c) :
    covarianceMatrix (measurementProjector k b * (matchGateCircuitOp gl * M))
      = bornWeight (matchGateCircuitOp gl * M) k b •
          measurementUpdate (covarianceRun gl (covarianceMatrix M)) k b := by
  rw [covarianceMatrix_measurement_eq_update (matchGateCircuitOp gl * M) k b hAway,
    covarianceMatrix_matchGateCircuit gl h M]

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
