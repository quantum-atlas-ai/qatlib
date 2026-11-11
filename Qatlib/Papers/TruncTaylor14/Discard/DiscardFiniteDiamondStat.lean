/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TruncTaylor14.Discard.DiscardLinearMap

/-!
# Specification of finite diamond-error discard simulation

This module states `SourceDiscardFiniteDiamond`, combining channel properties and circuit
resources for the Taylor reset-and-discard simulator. It requires finite diamond distance at
most `2⁻ᵏ` and an explicit trace-norm bound for every finite reference extension, together with
exact query and gate counts. See [BerryEtAl2015Taylor].

## Main statements

* `SourceDiscardFiniteDiamond`: Finite diamond-distance and circuit-resource specification.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 800000
namespace Qatlib.Papers.TruncTaylor14.DiscardCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- The proposition requiring the Taylor discard simulator to be completely positive and trace
preserving, have finite diamond distance at most `2⁻ᵏ` and reference trace-norm error at
most `2 * 2⁻ᵏ * ‖X‖₁`, and satisfy the stated circuit well-formedness and exact resource
counts under the simulation hypotheses. -/
def SourceDiscardFiniteDiamond : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D : ℕ)
    (h : J → ℝ) (U : J → Operator D) (j₀ : J) (t Λ : ℝ) (k : ℕ),
    (∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) →
    (∑ j, (h j : ℂ) • U j).IsHermitian → (∑ j, |h j|) ≤ Λ → 0 ≤ t →
    let r := max 1 (Nat.ceil (Λ * t / Real.log 2))
    let T := sourceTaylorDiscardChannel h U j₀ t Λ k
    let V := conjBranch (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t)
    CompletelyPositive T ∧ TracePreserving T ∧
    finiteDiamondDistance T V ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ∧
    (∀ (ref : ℕ) (X : Matrix (Fin D × Fin ref) (Fin D × Fin ref) ℂ),
      Matrix.traceNorm (tensorLeft T X - tensorLeft V X) ≤
        2 * (1 / 2 : ℝ) ^ k * Matrix.traceNorm X) ∧
    WellFormedAdjointCircuit (sourceTaylorDiscardWord (I := Fin D) h j₀
      (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) ∧
    adjointQueryCount (repeatAdjointWord (sourceTaylorDiscardWord (I := Fin D) h j₀
      (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) r) =
        3 * r * sourceDiscardCutoffKey r k ∧
    adjointGateCount (repeatAdjointWord (sourceTaylorDiscardWord (I := Fin D) h j₀
      (t / (r : ℝ)) (sourceDiscardCutoffKey r k)) r) =
        r * (6 * sourceDiscardCutoffKey r k + 12)

end Qatlib.Papers.TruncTaylor14.DiscardCore
