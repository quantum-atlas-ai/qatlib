/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionDefs
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
set_option warningAsError false
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

theorem flo_correlation_evolution {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (M : Fock n) :
    covarianceMatrix (matchGateCircuitOp gl * M) = covarianceRun gl (covarianceMatrix M) :=
  covarianceMatrix_matchGateCircuit gl h M

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
