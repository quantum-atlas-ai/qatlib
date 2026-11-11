/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation
import Qatlib.Concepts.OperatorAccess.EncodedAccess

/-!
# Purified Density Simulation Contract

`Corollary17DensitySimulation` states the response-word guarantee for the Hamiltonian
`purifiedDensity (Up *ᵥ Ket seed)`, given a unitary purification matrix `Up`. The contract
formalizes the purified-density application associated with Corollary 17 of [LowChuang2019].

For `0 < ε < 1`, it requests cosine and sine words over `parallelOracle (purificationBody Up)`
with exact query and gate counts. Their fourfold scaled compressions combine to approximate `exp
(-i t ρ)` in operator norm, with a degree budget linear in `|t|` and logarithmic in `1 / ε`.

## Main statements

* `Corollary17DensitySimulation` defines the approximation, degree, and resource requirements
  for a purified density matrix.

## References

- [Low and Chuang, 2019][LowChuang2019], Corollary 17.
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open scoped Matrix.Norms.L2Operator
open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.OperatorAccess.EncodedAccess Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers

/-- The simulation contract for the reduced density matrix prepared by a unitary from a basis
seed. For `0 < ε < 1`, it requires two response words with exact counts, degree at most `4 *
|t| + 8 * log (8 / ε) + 8`, and error at most `ε` for their scaled compressed combination. -/
def Corollary17DensitySimulation : Prop :=
  ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I],
    ∀ (Up : Matrix (A × I) (A × I) ℂ) (seed : A × I),
      Up ∈ Matrix.unitaryGroup (A × I) ℂ →
      ∀ (t ε : ℝ), 0 < ε → ε < 1 →
      ∃ (n : ℕ) (wc ws : List (AdjointStep (Bool × ((A × I) × I)))),
        (n : ℝ) ≤ 4 * |t| + 8 * Real.log (8 / ε) + 8 ∧
        adjointQueryCount wc = 2 * n ∧ adjointGateCount wc = 2 * n + 1 ∧
        adjointQueryCount ws = 2 * n + 1 ∧ adjointGateCount ws = 2 * n + 2 ∧
        ‖((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber seed))
              (evaluate (parallelOracle (purificationBody Up)) wc)
              (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber seed))
            - Complex.I • ((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber seed))
              (evaluate (parallelOracle (purificationBody Up)) ws)
              (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber seed)))
            - NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              purifiedDensity (Up *ᵥ Qatlib.Foundations.PureStateMath.Ket seed)))‖ ≤ ε

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
