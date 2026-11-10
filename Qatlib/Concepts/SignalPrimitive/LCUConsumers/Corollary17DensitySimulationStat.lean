/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation
import Qatlib.Concepts.OperatorAccess.EncodedAccess
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
