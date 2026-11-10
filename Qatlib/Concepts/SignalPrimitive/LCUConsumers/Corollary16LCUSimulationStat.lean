/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open scoped Matrix.Norms.L2Operator
open Matrix
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers

def Corollary16LCUSimulation : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    ∀ (U : J → Matrix I I ℂ), (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) → (∀ j, (U j)ᴴ = U j) →
      ∀ (w : J → ℝ), (∀ j, 0 ≤ w j) →
        ∀ (P : Matrix J J ℂ) (j₀ : J), Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsScaledPrepare P w (∑ j, w j) j₀ →
          ∀ (t ε : ℝ), 0 < ε → ε < 1 →
          ∃ (n : ℕ) (wc ws : List (AdjointStep (Bool × (J × I)))),
            (n : ℝ) ≤ 4 * |t * ∑ j, w j| + 8 * Real.log (8 / ε) + 8 ∧
            adjointQueryCount wc = 2 * n ∧ adjointGateCount wc = 2 * n + 1 ∧
            adjointQueryCount ws = 2 * n + 1 ∧ adjointGateCount ws = 2 * n + 2 ∧
            ‖((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
                  (evaluate (parallelOracle (Qatlib.Concepts.BlockEncoding.LinearCombination.LCUWorkspace U P)) wc)
                  (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
                - Complex.I • ((4 : ℂ) • compress (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀))
                  (evaluate (parallelOracle (Qatlib.Concepts.BlockEncoding.LinearCombination.LCUWorkspace U P)) ws)
                  (averageFrame (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber j₀)))
                - NormedSpace.exp ((-Complex.I * (t : ℂ)) • (∑ j, w j • U j)))‖ ≤ ε

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
