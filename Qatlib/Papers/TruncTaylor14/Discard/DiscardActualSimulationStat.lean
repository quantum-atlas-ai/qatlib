/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.TaylorDiscardSegment
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardDefinitions
import Qatlib.Papers.TruncTaylor14.Discard.Defs

/-!
# Specification of actual Taylor discard simulation

This module states the proposition `SourceDiscardActualSimulation` for unitary decompositions of
a finite Hermitian Hamiltonian. With a coefficient-sum bound and nonnegative time, it specifies
the segment count, circuit resource counts and amplification identity, and trace-norm error at
most `2⁻ᵏ` on density matrices. See [BerryEtAl2015Taylor].

## Main statements

* `SourceDiscardActualSimulation`: Joint circuit and state-error specification.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.TruncTaylor14.DiscardCore

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator ComplexOrder

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 800000

/-- The proposition requiring the selected Taylor discard circuit to be well formed with counts
`3 r K` and `r (6 K + 12)`, the stated amplification semantics, and final state trace-norm
error at most `2⁻ᵏ` under the unitary-decomposition and time hypotheses. -/
def SourceDiscardActualSimulation : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (t Λ : ℝ) (k : ℕ),
    (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
    (∑ j, (h j : ℂ) • U j).IsHermitian → (∑ j, |h j|) ≤ Λ → 0 ≤ t →
    let r := max 1 (Nat.ceil (Λ * t / Real.log 2))
    ((WellFormedAdjointCircuit (substituteAdjointCircuit (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k))))) ∧
      adjointQueryCount (repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k))))) r) = 3 * r * (sourceDiscardCutoffKey r k) ∧
      adjointGateCount (repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k))))) r) = r * (6 * (sourceDiscardCutoffKey r k) + 12)) ∧
    ((relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k)) (evaluate (taylorQuery U (sourceDiscardCutoffKey r k)) (substituteAdjointCircuit (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀ (sourceDiscardCutoffKey r k))))))) =
      -((relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k)) (evaluate (taylorQuery U (sourceDiscardCutoffKey r k)) (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)))) * FiberReflection (I := I) (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) * (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k)) (evaluate (taylorQuery U (sourceDiscardCutoffKey r k)) (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))))ᴴ *
          FiberReflection (I := I) (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) * (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k)) (evaluate (taylorQuery U (sourceDiscardCutoffKey r k)) (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)))))) ∧
    (∀ ρ : Matrix I I ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Matrix.traceNorm ((ResetDiscardStepCorrected (relabelGate (taylorDiscardEquiv J I (sourceDiscardCutoffKey r k)) (evaluate (taylorQuery U (sourceDiscardCutoffKey r k)) (taylorLCUWord h j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k)))) (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)))^[r] ρ -
        hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t * ρ * (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t)ᴴ) ≤
      (1 / 2 : ℝ)^k))

end Qatlib.Papers.TruncTaylor14.DiscardCore
