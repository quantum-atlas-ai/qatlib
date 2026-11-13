/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation

/-!
# Encoded Hamiltonian Simulation Contract

`Theorem1Simulation` specifies a Taylor-based approximation of `exp (-i t H)` from a projected
unitary encoding of `H / α` on the coordinate fiber `encodingFiber j₀`. It provides a concrete
response-word contract in the Hamiltonian simulation setting of [LowChuang2019], assuming a
positive normalization `α`, Hermiticity, a norm bound, and a suitable Taylor cutoff.

The conclusion consists of a cosine word with `2 * n` queries and a sine word with `2 * n + 1`
queries. Their fourfold scaled compressions through `averageFrame` combine with coefficient `-i`
to achieve operator-norm error at most `ε`.

## Main statements

* `Theorem1Simulation` defines the approximation and exact query and gate counts under the
  Taylor error hypotheses.

## References

- [Low and Chuang, 2019][LowChuang2019], Theorem 1.
-/

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

/-- The Taylor simulation contract for a Hermitian `H` with a projected unitary encoding of `H /
α`, positive `α`, and a cutoff meeting the stated Taylor hypotheses. It requires words with
query counts `2 * n` and `2 * n + 1` whose fourfold scaled compressed cosine-minus-i-sine
response approximates `exp (-i t H)` within `ε`. -/
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
