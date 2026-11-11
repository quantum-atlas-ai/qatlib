/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# LCU Simulation Contract

`Corollary16LCUSimulation` specifies Hamiltonian approximation for `H = ∑ j, w j • U j`, where
the `U j` are Hermitian unitaries and the weights are nonnegative. In the setting of Corollary
16 of [LowChuang2019], an `IsScaledPrepare` witness supplies the normalized LCU workspace.

The contract asks for two adjoint-query words, exact query and gate counts, and an operator-norm
error at most `ε` for the difference between their scaled compressed cosine-minus-i-sine
response and `exp (-i t H)`. The common degree parameter is bounded linearly in `|t * ∑ j, w j|`
and logarithmically in `1 / ε`.

## Main statements

* `Corollary16LCUSimulation` defines the quantified approximation and resource guarantee for `0
  < ε < 1`.

## References

- [Low and Chuang, 2019][LowChuang2019], Corollary 16.
-/

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

/-- The simulation contract for a nonnegative combination of Hermitian unitaries with a scaled
preparation witness. It requires cosine and sine words with explicit counts and a degree
bound whose scaled compressed combination approximates the Hamiltonian exponential within
`ε` for `0 < ε < 1`. -/
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
