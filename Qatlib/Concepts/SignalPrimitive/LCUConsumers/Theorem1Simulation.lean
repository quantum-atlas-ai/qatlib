/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers

def Theorem1Simulation : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    ∀ (H : Matrix I I ℂ) (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (α t ε : ℝ) (n : ℕ),
      H.IsHermitian → 0 < α → ‖H‖ ≤ α → 0 < ε → ε < 1 →
      ProjectedUnitaryEncoding (((α⁻¹ : ℝ) : ℂ) • H) V
        (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀) →
      2 * |t * α| ≤ (n : ℝ) + 1 →
        exponentialTaylorError (t * α) n ≤ ε →
      ∃ (wc ws : List (AdjointStep (Bool × (J × I)))),
        adjointQueryCount wc = 2 * n ∧ adjointGateCount wc = 2 * n + 1 ∧
        adjointQueryCount ws = 2 * n + 1 ∧ adjointGateCount ws = 2 * n + 2 ∧
        ‖((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
              (evaluate (parallelOracle V) wc) (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
            - Complex.I • ((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
              (evaluate (parallelOracle V) ws) (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀)))
            - NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))‖ ≤ ε

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
